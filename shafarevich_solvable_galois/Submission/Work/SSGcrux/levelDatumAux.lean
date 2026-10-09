import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.TPatom.noninvariantLevelDefs
import Submission.Work.SSGRoute.CycLevel.stabilizer_ofFinite_eq_decompositionSubgroup
import Submission.Work.SSGRoute.TatePoitouRoute.exists_shapiro_c
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.ramificationIdx_inertiaDeg_map_eq_of_ringEquiv
import Submission.Work.SSGRoute.TPatom.inertia_le_fixingSubgroup_of_ramificationIdx_eq_one
import Submission.Work.SSGRoute.Sha2Lib.smulHeightOneSpectrum_inv_liesOver
import Submission.Work.SSGRoute.Sha2Lib.under_smul_heightOneSpectrum
import Submission.Work.SSGcrux.zpowers_sup_inertia_eq_decomp_proved
import Submission.Work.SSGcrux.under_smul_eq_iff
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.exists_mem_decompositionSubgroup_restrictNormalHom_eq
import Submission.Commons.NumberTheory.NumberField.Completion.card_decompositionSubgroup_under_mul_card_ker
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local, cycle-free copies of two lemmas needed by `Work.SSGcrux.concentratedLevelData`

`Submission/Work/SSGcrux/concentratedLevelData.lean` cannot import
`Submission.Work.SSGcrux.noninvariantLevelDatum` (that module imports *it*, so the import would be
cyclic), and it therefore cannot import `Submission.Work.SSGRoute.TPatom.concentrationClause`
either.  This module provides cycle-free copies, under new names, of the two lemmas of those
modules that the assembly needs:

* `aux_decompK_le_fixingSubgroup_iff_split` (`Work.SSGcrux.decompK_le_fixingSubgroup_iff_split`),
* `aux_concentrationClause` (`Work.SSGRoute.TPatom.concentrationClause`).

The statements are unchanged; only the names differ.
-/

namespace Work.SSGcrux

open scoped NumberField Pointwise

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **The decomposition group is contained in the fixing subgroup of `F` iff `F` splits
completely at the place.** -/
theorem aux_decompK_le_fixingSubgroup_iff_split {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (F : IntermediateField K L) [FiniteDimensional K F] [IsGalois K F]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hQ : Q.asIdeal.LiesOver q.asIdeal) :
    SSGRoute.PTExt.decompK (k := K) (K := L) (NK.GlobalCFT.Place.ofFinite Q) ≤ F.fixingSubgroup ↔
      ((Q.asIdeal.under (NumberField.RingOfIntegers ↥F)).ramificationIdx
          (NumberField.RingOfIntegers K) = 1 ∧
        (Q.asIdeal.under (NumberField.RingOfIntegers ↥F)).inertiaDeg
          (NumberField.RingOfIntegers K) = 1) := by
  haveI : Normal K ↥F := inferInstance
  let q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥F) :=
    ⟨Q.asIdeal.under (NumberField.RingOfIntegers ↥F), inferInstance,
      Ideal.under_ne_bot _ Q.ne_bot⟩
  have hq'eq : q'.asIdeal = Q.asIdeal.under (NumberField.RingOfIntegers ↥F) := rfl
  have hq'q : q'.asIdeal.LiesOver q.asIdeal := by
    haveI : Q.asIdeal.LiesOver q'.asIdeal := by
      rw [hq'eq]; exact Ideal.over_under Q.asIdeal
    haveI : Q.asIdeal.LiesOver q.asIdeal := hQ
    exact Ideal.LiesOver.tower_bot Q.asIdeal q'.asIdeal q.asIdeal
  have hliesF : Q.asIdeal.LiesOver q'.asIdeal := by
    rw [hq'eq]; exact Ideal.over_under Q.asIdeal
  have hbridge : SSGRoute.PTExt.decompK (k := K) (K := L) (NK.GlobalCFT.Place.ofFinite Q)
      = Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) Q :=
    Work.SSGRoute.CycLevel.stabilizer_ofFinite_eq_decompositionSubgroup (K := K) Q
  rw [hbridge]
  have hker : F.fixingSubgroup
      = (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F).ker :=
    (IntermediateField.restrictNormalHom_ker (K := K) F).symm
  rw [hker, ← Subgroup.map_eq_bot_iff]
  have hmap : (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) Q).map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F)
      = Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q' := by
    apply le_antisymm
    · rintro _ ⟨σ, hσ, rfl⟩
      exact Commons.NumberTheory.NumberField.Completion.restrictNormalHom_mem_decompositionSubgroup
        F Q q' hq'eq hσ
    · intro τ hτ
      obtain ⟨σ, hσ⟩ :=
        Commons.NumberTheory.NumberField.Completion.exists_mem_decompositionSubgroup_restrictNormalHom_eq
          (K := K) (M := L) F q' Q hq'eq hliesF ⟨τ, hτ⟩
      exact ⟨σ, σ.2, hσ⟩
  rw [hmap,
    Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
      (K := K) q q' hq'q]
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers ↥F) q.asIdeal q'.asIdeal (↥F ≃ₐ[K] ↥F),
      Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers ↥F) q.asIdeal q'.asIdeal (↥F ≃ₐ[K] ↥F)]

section CfuncHelpers

open Work.SSGRoute.TatePoitouRoute

/-- `sect` is unchanged when a factor lying in `H` is appended. -/
lemma aux_sect_mul_mem {Γ : Type} [Group Γ] (H : Subgroup Γ) [H.Normal]
    (x : Γ) {d : Γ} (hd : d ∈ H) : sect H (x * d) = sect H x := by
  have hconj : x * d * x⁻¹ ∈ H := Subgroup.Normal.conj_mem (inferInstance : H.Normal) d hd x
  have h := sect_const H ⟨x * d * x⁻¹, hconj⟩ x
  rwa [show (x * d * x⁻¹) * x = x * d from by group] at h

/-- In a commutative group, `a * b * a⁻¹ = b`. -/
lemma aux_mul_conj_self {M : Type} [CommGroup M] (a b : M) : a * b * a⁻¹ = b := by
  rw [mul_comm a b, mul_assoc, mul_inv_cancel, mul_one]

/-- `cfunc H x d`, for `d ∈ H`, is the conjugate of `d` by the transversal defect `kappa H x`. -/
lemma aux_cfunc_eq_conj_mul {Γ : Type} [Group Γ] (H : Subgroup Γ) [H.Normal]
    (x : Γ) {d : Γ} (hd : d ∈ H) :
    cfunc H x d =
      kappa H x * (⟨x * d * x⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : H.Normal) d hd x⟩ : ↥H) *
          (kappa H x)⁻¹ := by
  apply Subtype.ext
  rw [coe_cfunc, aux_sect_mul_mem H x hd, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, kappa_coe]
  group

/-- The character `y` takes the same value on `cfunc H x d` and on the conjugate `x d x⁻¹`. -/
lemma aux_cfunc_yval {Γ : Type} [Group Γ] (H : Subgroup Γ) [H.Normal]
    {M : Type} [CommGroup M] (y : H →* M) (x : Γ) {d : Γ} (hd : d ∈ H) :
    y (cfunc H x d) =
      y (⟨x * d * x⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : H.Normal) d hd x⟩ : ↥H) := by
  rw [aux_cfunc_eq_conj_mul H x hd, map_mul, map_mul, map_inv]
  exact aux_mul_conj_self _ _

end CfuncHelpers

/-- Concentration clause: with `K1L` the level of the fixed field of `N` inside `L`, `EL` the image of the concentrated Grünwald extension (finite Galois of degree p over K1L), `y` the character of `H = N.comap galRes` killing exactly the automorphisms fixing `EL` pointwise, `q'` a prime of `L`, `d` a Frobenius at `q'` over `k` with `d ^ f ∈ H` for `f` the inertia degree of `q' ∩ K1L` over `q' ∩ k`, `u₀'` the detecting prime, `hsplit` the split-inert dictionary and `hu₀'` the prime bookkeeping, one has for every `x : Gal(L/k)`: `y (cfunc H x (d ^ f)) = 1 ↔ galRes x ∉ concSet k K w N γ`. Route: cfunc is `sect H x * d^f * (sect H x)⁻¹`, whose y-value equals that of `x d^f x⁻¹` (abelian target, normal kernel); by `hy` this is 1 iff `x d^f x⁻¹` fixes `EL`; using the mod-inertia generation at the prime `xq'` (`Work.SSGcrux.zpowers_sup_inertia_eq_decomp_proved` with `K := K1L`, conjugated, using `NK.Chebotarev.IsFrobAtConj`) and `I_{xq'} ≤ Gal(L/EL)` from `hsplit`, that is equivalent to `D_{xq'}(L/K1L) ≤ Gal(L/EL)`; by `Work.SSGcrux.aux_decompK_le_fixingSubgroup_iff_split` and `hsplit`, to `xq' ∩ K1L ≠ u₀'`; and by `hu₀'` to `galRes x ∉ concSet`. -/
theorem aux_concentrationClause
    {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    (p : ℕ) [Fact p.Prime] (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (K1L : IntermediateField k L) (EL : IntermediateField K1L L)
    [FiniteDimensional k K1L] [NumberField K1L] [FiniteDimensional K1L EL]
    (hH : N.comap (SSGRoute.PTExt.galRes k K L) = K1L.fixingSubgroup)
    (hgalEL : IsGalois K1L EL) (hgalK1LL : IsGalois K1L L)
    (y : (N.comap (SSGRoute.PTExt.galRes k K L) : Type) →* Multiplicative (ZMod p))
    (hy : ∀ σ : (N.comap (SSGRoute.PTExt.galRes k K L) : Type),
      y σ = 1 ↔ ∀ x : L, x ∈ EL → (σ : L ≃ₐ[k] L) x = x)
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (d : L ≃ₐ[k] L) (f : ℕ)
    (hdFrob : NK.Chebotarev.IsFrobAt (K := k) (L := L) q' d)
    (hdH : d ^ f ∈ N.comap (SSGRoute.PTExt.galRes k K L))
    (hfdeg : f = (q'.asIdeal.under (NumberField.RingOfIntegers K1L)).inertiaDeg
      (NumberField.RingOfIntegers k))
    (w : NK.GlobalCFT.Place K) (γ : K ≃ₐ[k] K)
    (u₀' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K1L))
    (hu₀' : ∀ x : L ≃ₐ[k] L,
      ((NK.GlobalCFT.Place.smulHeightOneSpectrum x q').asIdeal.under
          (NumberField.RingOfIntegers K1L) = u₀'.asIdeal ↔
        SSGRoute.PTExt.galRes k K L x ∈ Work.SSGRoute.TPatom.concSet k K w N γ))
    (hsplit : ∀ p' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K1L),
      p'.asIdeal.LiesOver (q'.asIdeal.under (NumberField.RingOfIntegers k)) →
      ∀ 𝔮' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers EL),
        𝔮'.asIdeal.LiesOver p'.asIdeal →
          𝔮'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K1L) = 1 ∧
          (𝔮'.asIdeal.inertiaDeg (NumberField.RingOfIntegers K1L) = 1 ↔ p' ≠ u₀')) :
    ∀ x : L ≃ₐ[k] L,
      y (Work.SSGRoute.TatePoitouRoute.cfunc (N.comap (SSGRoute.PTExt.galRes k K L)) x
          (⟨d ^ f, hdH⟩ : (N.comap (SSGRoute.PTExt.galRes k K L) : Type))) = 1 ↔
        SSGRoute.PTExt.galRes k K L x ∉ Work.SSGRoute.TPatom.concSet k K w N γ := by
  intro x
  classical
  haveI hgalK1L' : IsGalois ↥K1L L := hgalK1LL
  haveI hgalEL' : IsGalois ↥K1L ↥EL := hgalEL
  haveI hfinK1LL : FiniteDimensional ↥K1L L :=
    Module.Finite.of_restrictScalars_finite k ↥K1L L
  -- ### `Gal(K1L/k)` is Galois, from `hH`
  have hnormH : (N.comap (SSGRoute.PTExt.galRes k K L)).Normal :=
    Subgroup.Normal.comap (inferInstance : N.Normal) (SSGRoute.PTExt.galRes k K L)
  have hK1L_eq : K1L = IntermediateField.fixedField (N.comap (SSGRoute.PTExt.galRes k K L)) := by
    rw [hH, IsGalois.fixedField_fixingSubgroup]
  haveI hgalK1L : IsGalois k ↥K1L := hK1L_eq ▸ (inferInstance : IsGalois k
    ↥(IntermediateField.fixedField (N.comap (SSGRoute.PTExt.galRes k K L))))
  -- ### The conjugated element `x * d ^ f * x⁻¹ ∈ H`
  have hconj : x * d ^ f * x⁻¹ ∈ N.comap (SSGRoute.PTExt.galRes k K L) :=
    Subgroup.Normal.conj_mem hnormH (d ^ f) hdH x
  have hmemK1 : x * d ^ f * x⁻¹ ∈ K1L.fixingSubgroup := by
    rw [← hH]; exact hconj
  -- ### The element `e₁ : Gal(L/K1L)` corresponding to `x * d ^ f * x⁻¹`
  let e₁ : L ≃ₐ[↥K1L] L :=
    IntermediateField.fixingSubgroupEquiv K1L ⟨x * d ^ f * x⁻¹, hmemK1⟩
  have he₁ : ∀ z : L, e₁ z = (x * d ^ f * x⁻¹) z := fun z => rfl
  -- ### The prime `Q = x q'` and the primes below it
  let Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) :=
    NK.GlobalCFT.Place.smulHeightOneSpectrum x q'
  let p' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1L) :=
    ⟨Q.asIdeal.under (NumberField.RingOfIntegers ↥K1L), inferInstance,
      Ideal.under_ne_bot _ Q.ne_bot⟩
  let 𝔮' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥EL) :=
    ⟨Q.asIdeal.under (NumberField.RingOfIntegers ↥EL), inferInstance,
      Ideal.under_ne_bot _ Q.ne_bot⟩
  -- ### `p'` lies over `q' ∩ k`, `𝔮'` lies over `p'`
  have hlies : p'.asIdeal.LiesOver (q'.asIdeal.under (NumberField.RingOfIntegers k)) :=
    Ideal.LiesOver.mk (by
      show Ideal.under (NumberField.RingOfIntegers k) q'.asIdeal =
        Ideal.under (NumberField.RingOfIntegers k) p'.asIdeal
      rw [show p'.asIdeal = Ideal.under (NumberField.RingOfIntegers ↥K1L) Q.asIdeal from rfl,
        Ideal.under_under, Work.SSGRoute.Sha2Lib.under_smulHeightOneSpectrum x q'])
  have hqq : 𝔮'.asIdeal.LiesOver p'.asIdeal :=
    Ideal.LiesOver.mk (by
      show p'.asIdeal = Ideal.under (NumberField.RingOfIntegers ↥K1L) 𝔮'.asIdeal
      rw [show 𝔮'.asIdeal = Ideal.under (NumberField.RingOfIntegers ↥EL) Q.asIdeal from rfl,
        Ideal.under_under,
        show p'.asIdeal = Ideal.under (NumberField.RingOfIntegers ↥K1L) Q.asIdeal from rfl])
  obtain ⟨hram, hinert⟩ := hsplit p' hlies 𝔮' hqq
  -- ### The Frobenius at `x q'`
  have hd' : NK.Chebotarev.IsFrobAt (K := k) (L := L) Q (x * d * x⁻¹) := by
    have h := NK.Chebotarev.IsFrobAtConj (K := k) (L := L) (P := q') (σ := d) (τ := x) hdFrob
    rwa [Work.SSGcrux.smul_primeIdeal_eq_smulHeightOneSpectrum' x q'] at h
  -- ### The exponent identity
  have he' : AlgEquiv.restrictScalars k e₁ = (x * d * x⁻¹) ^ f := by
    ext z
    rw [AlgEquiv.restrictScalars_apply]
    show e₁ z = ((x * d * x⁻¹) ^ f) z
    rw [conj_pow]
    rfl
  -- ### The inertia degree identity
  have hQu : Ideal.under (NumberField.RingOfIntegers ↥K1L) Q.asIdeal =
      Ideal.map (↑(NK.GlobalCFT.Place.ringOfIntegersEquiv (AlgEquiv.restrictNormal x K1L)) :
          NumberField.RingOfIntegers ↥K1L →+* NumberField.RingOfIntegers ↥K1L)
        (Ideal.under (NumberField.RingOfIntegers ↥K1L) q'.asIdeal) :=
    Work.SSGRoute.Sha2Lib.under_smul_heightOneSpectrum (k := k) (K := ↥K1L) (L := L) x q'
  have hdf : (Q.asIdeal.under (NumberField.RingOfIntegers ↥K1L)).inertiaDeg
        (NumberField.RingOfIntegers k) =
      (q'.asIdeal.under (NumberField.RingOfIntegers ↥K1L)).inertiaDeg
        (NumberField.RingOfIntegers k) := by
    rw [show Q.asIdeal.under (NumberField.RingOfIntegers ↥K1L) =
        Ideal.map (↑(NK.GlobalCFT.Place.ringOfIntegersEquiv (AlgEquiv.restrictNormal x K1L)) :
            NumberField.RingOfIntegers ↥K1L →+* NumberField.RingOfIntegers ↥K1L)
          (Ideal.under (NumberField.RingOfIntegers ↥K1L) q'.asIdeal) from hQu]
    exact (Work.SSGRoute.TatePoitouRoute.FinitenessHM.ramificationIdx_inertiaDeg_map_eq_of_ringEquiv
      (NK.GlobalCFT.Place.ringOfIntegersEquiv (AlgEquiv.restrictNormal x K1L))
      (Ideal.under (NumberField.RingOfIntegers ↥K1L) q'.asIdeal)
      (fun r => Work.SSGRoute.Sha2Lib.ringOfIntegersEquiv_algebraMap
        (AlgEquiv.restrictNormal x K1L) r)).2
  have hf' : f = (Q.asIdeal.under (NumberField.RingOfIntegers ↥K1L)).inertiaDeg
      (NumberField.RingOfIntegers k) := hfdeg.trans hdf.symm
  -- ### The mod-inertia generation at `x q'`
  have hsup := Work.SSGcrux.zpowers_sup_inertia_eq_decomp_proved (k := k) (K := ↥K1L) (L := L)
    Q (x * d * x⁻¹) e₁ f hd' he' hf'
  have hDS : Submission.NeukirchUchida.Local.decompositionSubgroup Q =
      SSGRoute.PTExt.decompK (k := ↥K1L) (K := L) (NK.GlobalCFT.Place.ofFinite Q) := by
    ext δ
    rw [Work.SSGRoute.Sha2Lib.mem_stabilizer_ofFinite_iff_decompositionSubgroup]
  have hsup' : Subgroup.zpowers e₁ ⊔ Ideal.inertia (L ≃ₐ[↥K1L] L) Q.asIdeal =
      SSGRoute.PTExt.decompK (k := ↥K1L) (K := L) (NK.GlobalCFT.Place.ofFinite Q) :=
    hsup.trans hDS
  -- ### The inertia subgroup lies in the fixing subgroup of `EL`
  have hI_le : Ideal.inertia (L ≃ₐ[↥K1L] L) Q.asIdeal ≤ EL.fixingSubgroup :=
    Work.SSGRoute.TPatom.inertia_le_fixingSubgroup_of_ramificationIdx_eq_one
      (k := ↥K1L) (M := L) EL Q hram
  -- ### Step 3: `e₁ ∈ Fix(EL) ↔ D ≤ Fix(EL)`
  have hstep3 : e₁ ∈ EL.fixingSubgroup ↔
      SSGRoute.PTExt.decompK (k := ↥K1L) (K := L) (NK.GlobalCFT.Place.ofFinite Q) ≤
        EL.fixingSubgroup := by
    rw [← hsup']
    exact ⟨fun he => sup_le (Subgroup.zpowers_le.mpr he) hI_le,
      fun hD => hD (Subgroup.mem_sup_left (Subgroup.mem_zpowers e₁))⟩
  -- ### Step 4: via the split/inert dictionary
  have hstep4 : SSGRoute.PTExt.decompK (k := ↥K1L) (K := L) (NK.GlobalCFT.Place.ofFinite Q) ≤
      EL.fixingSubgroup ↔ p' ≠ u₀' := by
    rw [Work.SSGcrux.aux_decompK_le_fixingSubgroup_iff_split (K := ↥K1L) (L := L) (F := EL)
      (q := p') (Q := Q) (Ideal.over_under Q.asIdeal)]
    exact ⟨fun h => hinert.mp h.2, fun h => ⟨hram, hinert.mpr h⟩⟩
  -- ### Step 5: the prime bookkeeping
  have hstep5 : p' ≠ u₀' ↔
      SSGRoute.PTExt.galRes k K L x ∉ Work.SSGRoute.TPatom.concSet k K w N γ := by
    have hpu : (p' = u₀') ↔ (p'.asIdeal = u₀'.asIdeal) :=
      IsDedekindDomain.HeightOneSpectrum.ext_iff
    have hA : (p'.asIdeal = u₀'.asIdeal) ↔
        SSGRoute.PTExt.galRes k K L x ∈ Work.SSGRoute.TPatom.concSet k K w N γ := by
      rw [show p'.asIdeal = (NK.GlobalCFT.Place.smulHeightOneSpectrum x q').asIdeal.under
          (NumberField.RingOfIntegers ↥K1L) from rfl]
      exact hu₀' x
    exact not_congr (hpu.trans hA)
  -- ### Step 2: the character `y` sees `EL.fixingSubgroup`
  have hstep2 : y (⟨x * d ^ f * x⁻¹, hconj⟩ :
        ↥(N.comap (SSGRoute.PTExt.galRes k K L))) = 1 ↔ e₁ ∈ EL.fixingSubgroup := by
    rw [hy ⟨x * d ^ f * x⁻¹, hconj⟩, IntermediateField.mem_fixingSubgroup_iff]
    exact Iff.rfl
  -- ### Step 1: `y (cfunc ...) = y ⟨x d^f x⁻¹⟩`
  have hstep1 : y (Work.SSGRoute.TatePoitouRoute.cfunc (N.comap (SSGRoute.PTExt.galRes k K L)) x
        (⟨d ^ f, hdH⟩ : ↥(N.comap (SSGRoute.PTExt.galRes k K L)))) =
      y (⟨x * d ^ f * x⁻¹, hconj⟩ :
        ↥(N.comap (SSGRoute.PTExt.galRes k K L))) := by
    simpa using aux_cfunc_yval (N.comap (SSGRoute.PTExt.galRes k K L)) y x hdH
  rw [hstep1]
  exact hstep2.trans (hstep3.trans (hstep4.trans hstep5))

/-- **Transport of Galois-ness and degree along a compatible pair of `k`-algebra isomorphisms.** -/
theorem aux_isGalois_finrank_of_base_algEquiv
    {k F F' E E' : Type} [Field k] [Field F] [Field F'] [Field E] [Field E']
    [Algebra k F] [Algebra k F'] [Algebra k E] [Algebra k E'] [Algebra F E] [Algebra F' E']
    [IsScalarTower k F E] [IsScalarTower k F' E']
    [FiniteDimensional k F] [FiniteDimensional F E] [IsGalois F E]
    (eF : F ≃ₐ[k] F') (eE : E ≃ₐ[k] E')
    (hcompat : ∀ (a : F) (x : E), eE (a • x) = eF a • eE x) :
    FiniteDimensional F' E' ∧ IsGalois F' E' ∧
      Module.finrank F' E' = Module.finrank F E := by
  have hcomp : (algebraMap F' E').comp (eF.toRingEquiv : F →+* F')
      = (eE.toRingEquiv : E →+* E').comp (algebraMap F E) :=
    RingHom.ext (fun a => by
      show algebraMap F' E' (eF a) = eE (algebraMap F E a)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      simpa using (hcompat a 1).symm)
  haveI hF' : FiniteDimensional k F' := eF.toLinearEquiv.finiteDimensional
  haveI hE : FiniteDimensional k E := FiniteDimensional.trans k F E
  haveI hE' : FiniteDimensional k E' := eE.toLinearEquiv.finiteDimensional
  refine ⟨Module.Finite.of_restrictScalars_finite k F' E',
    IsGalois.of_equiv_equiv hcomp, ?_⟩
  have h1 : Module.finrank k F' * Module.finrank F' E' = Module.finrank k E' :=
    Module.finrank_mul_finrank k F' E'
  have h2 : Module.finrank k F * Module.finrank F E = Module.finrank k E :=
    Module.finrank_mul_finrank k F E
  have hk : Module.finrank k E' = Module.finrank k E :=
    LinearEquiv.finrank_eq eE.toLinearEquiv.symm
  have hf : Module.finrank k F' = Module.finrank k F :=
    LinearEquiv.finrank_eq eF.toLinearEquiv.symm
  rw [hf, hk] at h1
  exact Nat.mul_left_cancel (Module.finrank_pos (R := k) (M := F)) (by rw [h1, h2])

end Work.SSGcrux
