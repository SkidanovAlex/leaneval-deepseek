import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.E9Nodes.e9_baseS
import Submission.Work.SSGRoute.lam_local_determination
import Submission.Work.SSGRoute.extHRestrict_eq_zero_of_le
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E9b

open SSGRoute.PTExt

set_option maxHeartbeats 800000

/-! ## Conjugacy of the inertia condition

The inertia condition `IsInertiaAt q σ` is "σ acts trivially on the residue field of `q`", and it
is conjugation-equivariant: `τ` is inertia at `σ • q` iff `σ⁻¹ τ σ` is inertia at `q`.  This is
the place-level input for the independence of unramifiedness from the chosen place above a fixed
place below. -/

/-- The inertia condition rewritten as a membership condition for the prime ideal. -/
private lemma inertiaConj_forall_mem {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (σ : L ≃ₐ[k] L) :
    IsInertiaAt q σ ↔
      ∀ x : NumberField.RingOfIntegers L, σ • x - x ∈ q.asIdeal := by
  unfold IsInertiaAt
  refine forall_congr' fun x => ?_
  have key : ((σ • x - x : NumberField.RingOfIntegers L) : L) = σ (x : L) - (x : L) := by
    have h : algebraMap (NumberField.RingOfIntegers L) L (σ • x - x) =
        algebraMap (NumberField.RingOfIntegers L) L (σ • x) -
          algebraMap (NumberField.RingOfIntegers L) L x := map_sub _ _ _
    rw [show ((σ • x - x : NumberField.RingOfIntegers L) : L) =
        algebraMap (NumberField.RingOfIntegers L) L (σ • x - x) from rfl, h]
    congr 1
  rw [← key]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) (v := q) _

/-- `τ • (σ • y) - σ • y` is the image under `σ` of `(σ⁻¹ τ σ) • y - y`. -/
private lemma inertiaConj_sub_eq {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] (σ τ : L ≃ₐ[k] L)
    (y : NumberField.RingOfIntegers L) :
    τ • (σ • y) - σ • y =
      NK.GlobalCFT.Place.ringOfIntegersEquiv σ ((σ⁻¹ * τ * σ) • y - y) := by
  rw [show NK.GlobalCFT.Place.ringOfIntegersEquiv σ ((σ⁻¹ * τ * σ) • y - y)
      = σ • ((σ⁻¹ * τ * σ) • y - y) from rfl, smul_sub]
  rw [← mul_smul τ σ y]
  have hgroup : τ * σ = σ * (σ⁻¹ * τ * σ) := by group
  rw [hgroup, mul_smul]

/-- **Conjugacy of the inertia condition.**  For `σ, τ ∈ Gal(L/k)` and a nonzero prime `q` of
`𝓞 L`, the element `τ` lies in the inertia group of the image prime `σ • q` if and only if
`σ⁻¹ τ σ` lies in the inertia group of `q`. -/
theorem isInertiaAt_smulHeightOneSpectrum_iff {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (σ τ : L ≃ₐ[k] L) :
    IsInertiaAt (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q) τ ↔
      IsInertiaAt q (σ⁻¹ * τ * σ) := by
  rw [inertiaConj_forall_mem, inertiaConj_forall_mem]
  constructor
  · intro h y
    have h1 : τ • (σ • y) - σ • y ∈
        (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q).asIdeal := h (σ • y)
    rw [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal, inertiaConj_sub_eq σ τ y] at h1
    rwa [Ideal.apply_mem_of_equiv_iff] at h1
  · intro h x
    have hx : σ • (σ⁻¹ • x) = x := by rw [← mul_smul, mul_inv_cancel, one_smul]
    have h1 : (σ⁻¹ * τ * σ) • (σ⁻¹ • x) - σ⁻¹ • x ∈ q.asIdeal := h (σ⁻¹ • x)
    rw [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal, ← hx,
      inertiaConj_sub_eq σ τ (σ⁻¹ • x)]
    exact Ideal.mem_map_of_mem _ h1

/-! ## Conjugation transfer of vanishing of the restriction

`extHRestrict D h = 0` is invariant under replacing `D` by a conjugate subgroup.  The forward
implication of the equivalence is `Work.SSGRoute.extHRestrict_conj_eq_zero`; the reverse one is
obtained by conjugating back. -/

/-- `extHRestrict` vanishes on a subgroup iff it vanishes on a conjugate of it. -/
theorem extHRestrict_map_conj_eq_zero_iff {G : Type} [Group G] (D : Subgroup G) (g : G)
    {A : Rep SSGRoute.PTExt.Coeff G} (y : extH A 1) :
    extHRestrict (D.map (MulAut.conj g).toMonoidHom) y = 0 ↔ extHRestrict D y = 0 := by
  refine ⟨fun h => ?_, fun h => Work.SSGRoute.extHRestrict_conj_eq_zero D g y h⟩
  have h2 := Work.SSGRoute.extHRestrict_conj_eq_zero
    (D.map (MulAut.conj g).toMonoidHom) g⁻¹ y h
  have hDeq : (D.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = D := by
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom
        = MonoidHom.id G := by
      ext x
      show (MulAut.conj g⁻¹) ((MulAut.conj g) x) = x
      rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]
      group
    rw [hcomp, Subgroup.map_id]
  rwa [hDeq] at h2

/-! ## The main independence statement -/

/-- Unramifiedness at `q` is the same as unramifiedness at the image prime `σ • q`. -/
theorem isUnramifiedClassAt_smulHeightOneSpectrum_iff {k L : Type} [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    {M : Rep SSGRoute.PTExt.Coeff (L ≃ₐ[k] L)}
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (σ : L ≃ₐ[k] L) (h : extH M 1) :
    IsUnramifiedClassAt q h ↔
      IsUnramifiedClassAt (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q) h := by
  constructor
  · intro hh D' hD'
    have hD : ∀ δ ∈ D'.map (MulAut.conj σ⁻¹).toMonoidHom, IsInertiaAt q δ := by
      intro δ hδ
      obtain ⟨τ, hτ, hτδ⟩ := Subgroup.mem_map.mp hδ
      have hval : (MulAut.conj σ⁻¹).toMonoidHom τ = σ⁻¹ * τ * σ := by
        show (MulAut.conj σ⁻¹) τ = σ⁻¹ * τ * σ
        rw [MulAut.conj_apply, inv_inv]
      rw [← hτδ, hval]
      exact (isInertiaAt_smulHeightOneSpectrum_iff q σ τ).mp (hD' τ hτ)
    have hzero : extHRestrict (D'.map (MulAut.conj σ⁻¹).toMonoidHom) h = 0 := hh _ hD
    exact (extHRestrict_map_conj_eq_zero_iff D' σ⁻¹ h).mp hzero
  · intro hh D hD
    have hD' : ∀ δ ∈ D.map (MulAut.conj σ).toMonoidHom,
        IsInertiaAt (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q) δ := by
      intro δ hδ
      obtain ⟨τ, hτ, hτδ⟩ := Subgroup.mem_map.mp hδ
      have hval : (MulAut.conj σ).toMonoidHom τ = σ * τ * σ⁻¹ := by
        show (MulAut.conj σ) τ = σ * τ * σ⁻¹
        rw [MulAut.conj_apply]
      rw [← hτδ, hval]
      refine (isInertiaAt_smulHeightOneSpectrum_iff q σ (σ * τ * σ⁻¹)).mpr ?_
      rw [show σ⁻¹ * (σ * τ * σ⁻¹) * σ = τ by group]
      exact hD τ hτ
    have hzero : extHRestrict (D.map (MulAut.conj σ).toMonoidHom) h = 0 := hh _ hD'
    exact (extHRestrict_map_conj_eq_zero_iff D σ h).mp hzero

/-- **Unramifiedness is independent of the place chosen above a fixed place below.**  Let
`L/k` be a finite Galois extension of number fields, `v` a place of `k`, and `q`, `q'` two finite
places of `L` above `v`.  Then `h ∈ H¹(Gal(L/k), M)` is unramified at `q` if and only if it is
unramified at `q'`. -/
theorem isUnramifiedClassAt_conj {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    {M : Rep SSGRoute.PTExt.Coeff (L ≃ₐ[k] L)}
    (v : NK.GlobalCFT.Place k)
    (q q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q) v)
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') v)
    (h : SSGRoute.PTExt.extH M 1) :
    SSGRoute.PTExt.IsUnramifiedClassAt q h ↔ SSGRoute.PTExt.IsUnramifiedClassAt q' h := by
  obtain ⟨σ, hσ⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver (K := k) (L := L) hq hq'
  have hσq : NK.GlobalCFT.Place.smulHeightOneSpectrum σ q = q' := by
    rw [← NK.GlobalCFT.Place.ofFinite_inj]
    simpa using hσ
  rw [← hσq]
  exact isUnramifiedClassAt_smulHeightOneSpectrum_iff (M := M) q σ h

end Work.SSGRoute.E9b
