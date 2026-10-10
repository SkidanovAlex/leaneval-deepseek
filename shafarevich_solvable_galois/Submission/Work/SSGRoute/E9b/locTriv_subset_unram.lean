import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E9b.isInertiaAt_mem_stabilizer_ofFinite
import Submission.Work.SSGRoute.extHRestrict_eq_zero_of_le
import Submission.Work.SSGRoute.lam_local_determination
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise

namespace Work.SSGRoute.E9b

/-! ## Locally trivial at one place implies unramified at every place over its base

`IsUnramifiedClassAt q h` asks that `h ∈ H¹(Gal(L/k), M)` restrict to `0` on every subgroup of the
inertia group `I_q` of the finite place `q`.  Since `I_q ≤ D_q` (the decomposition group, i.e. the
stabiliser of `q` acting on the places of `L`), it suffices to kill `h` on `D_q`.  If `h` is killed
on the stabiliser of *some* place `w` above the same place `v` of `k`, then `h` is killed on `D_q`
too: the places above `v` form one Galois orbit, so `D_q = g D_w g⁻¹` for some `g`, and restriction
to a conjugate subgroup vanishes whenever restriction to the subgroup does
(`Work.SSGRoute.extHRestrict_conj_eq_zero`).

The two ingredients of a non-cohomological nature are
`Work.SSGRoute.E9b.isInertiaAt_mem_stabilizer_ofFinite` (`I_q ≤ D_q`) and
`NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver` (the orbit is a single place). -/

/-- **Locally trivial at a place implies unramified at every place over the same place below.**
Let `L/k` be a finite Galois extension of number fields, `v` a place of `k`, and `w`, `q` two places
of `L` above `v` with `q` finite.  If `h ∈ H¹(Gal(L/k), M)` has vanishing restriction to the
decomposition group `stab w`, then `h` is unramified at `q`. -/
theorem locTriv_subset_unram {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (M : Rep SSGRoute.PTExt.Coeff (L ≃ₐ[k] L))
    (v : NK.GlobalCFT.Place k) (w : NK.GlobalCFT.Place L)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hw : NK.GlobalCFT.Place.LiesOver w v)
    (hq : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q) v)
    (h : SSGRoute.PTExt.extH M 1)
    (hh : SSGRoute.PTExt.extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w) h = 0) :
    SSGRoute.PTExt.IsUnramifiedClassAt q h := by
  intro D hD
  -- Every subgroup of the inertia group of `q` sits inside the decomposition group of `q`.
  have hDle : D ≤ MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q) :=
    fun σ hσ => isInertiaAt_mem_stabilizer_ofFinite q σ (hD σ hσ)
  -- `w` and `Place.ofFinite q` lie over the same place `v` of `k`, hence are conjugate.
  obtain ⟨g, hg⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver hw hq
  -- Therefore the decomposition group of `q` is conjugate to `stab w`, where `h` dies.
  have hstab : SSGRoute.PTExt.extHRestrict
      (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q)) h = 0 := by
    rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj g w]
    exact extHRestrict_conj_eq_zero (MulAction.stabilizer (L ≃ₐ[k] L) w) g h hh
  exact extHRestrict_eq_zero_of_le D _ hDle h hstab

end Work.SSGRoute.E9b
