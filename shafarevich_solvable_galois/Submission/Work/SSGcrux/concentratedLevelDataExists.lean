import Mathlib.Computability.Reduce
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.Sha2Lib.coprime_ramificationIdx_of_inertia_eq_bot
import Submission.Work.SSGRoute.Sha2Lib.exists_cyclic_p_level_split_inert
import Submission.Work.SSGRoute.Sha2Lib.normalClosureEqTop
import Submission.Work.SSGRoute.TPatom.EL_split_inert_dictionary
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.ramificationIdx_inertiaDeg_map_eq_of_ringEquiv
import Submission.Work.SSGate.fixedField_ramificationIdx_eq_one
import Submission.Work.SSGate.inertia_eq_bot_of_concentrated_level
import Submission.Work.SSGcrux.exists_char_ker_fixingSubgroup
import Submission.Work.SSGcrux.normalClosure_inertia_le_fixingSubgroup
import Submission.Work.SSGcrux.under_eq_iff_mem_concSet
import Submission.Work.SSGcrux.zpowers_sup_inertia_eq_decomp_proved
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.SSGcrux.PT

open scoped NumberField Pointwise

/-- **A generator of `D ⊓ H` from a generator of `D`.** -/
theorem zpowers_pow_eq_inf {Γ : Type} [Group Γ] [Fintype Γ] (D H : Subgroup Γ) (d : Γ) (f : ℕ)
    (hcyc : Subgroup.zpowers d = D) (hf : f ∣ Nat.card ↥D) (hdH : d ^ f ∈ H)
    (hcard : Nat.card ↥(D ⊓ H) * f = Nat.card ↥D) :
    Subgroup.zpowers (d ^ f) = D ⊓ H := by
  have hdD : d ∈ D := hcyc ▸ Subgroup.mem_zpowers d
  have hle : Subgroup.zpowers (d ^ f) ≤ D ⊓ H := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.mpr ⟨D.pow_mem hdD f, hdH⟩
  have hfpos : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · exfalso
      rw [h, mul_zero] at hcard
      exact (Nat.card_pos (α := ↥D)).ne' hcard.symm
    · exact h
  have hord : orderOf d = Nat.card ↥D := by
    rw [← Nat.card_zpowers, hcyc]
  have hcard_z : Nat.card ↥(Subgroup.zpowers (d ^ f)) = Nat.card ↥(D ⊓ H) := by
    rw [Nat.card_zpowers, orderOf_pow, hord, Nat.gcd_eq_right hf, ← hcard,
      Nat.mul_div_left _ hfpos]
  exact Subgroup.eq_of_le_of_card_ge hle hcard_z.symm.le

/-- **Block membership dictionary.**  `galRes σ` lies in the block `γ · D_w · N` iff `σ` lies in
the corresponding `(H, D_{q'})`-double coset `H · σ₀ · D_{q'}` (`σ₀` a lift of `γ`). -/
theorem galRes_mem_concSet_iff {k K L : Type} [Field k] [Field K] [Field L] [NumberField k]
    [NumberField K] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    [IsGalois k L]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq' : q'.asIdeal.LiesOver q.asIdeal)
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (σ₀ σ : L ≃ₐ[k] L) (γ : K ≃ₐ[k] K)
    (hγ : SSGRoute.PTExt.galRes k K L σ₀ = γ) :
    SSGRoute.PTExt.galRes k K L σ ∈ Work.SSGRoute.TPatom.concSet k K w N γ ↔
      ∃ h ∈ N.comap (SSGRoute.PTExt.galRes k K L),
        ∃ δ ∈ SSGRoute.PTExt.decompK (k := k) (K := L) (NK.GlobalCFT.Place.ofFinite q'),
          σ = h * σ₀ * δ := by
  have hlies : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w := by
    rw [hwq]; exact NK.GlobalCFT.Place.liesOver_ofFinite hq'
  obtain ⟨fd, hfd⟩ := Work.SSGRoute.decompK_restrict_exists k K L w
    (NK.GlobalCFT.Place.ofFinite q') hlies
  have hfsurj := Work.SSGRoute.decompK_restrict_surjective k K w L
    (NK.GlobalCFT.Place.ofFinite q') hlies fd hfd
  have hgalδ : ∀ δ : ↥(SSGRoute.PTExt.decompK (k := k) (K := L)
      (NK.GlobalCFT.Place.ofFinite q')), SSGRoute.PTExt.galRes k K L (δ : L ≃ₐ[k] L)
      ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w := by
    intro δ
    have h := (fd δ).2
    rw [hfd δ] at h
    exact h
  constructor
  · intro hmem
    simp only [Work.SSGRoute.TPatom.concSet] at hmem
    obtain ⟨δw, hδw, n, hn, hgn⟩ := hmem
    obtain ⟨δ₀, hδ₀⟩ := hfsurj ⟨δw, hδw⟩
    refine ⟨σ * (σ₀ * (δ₀ : L ≃ₐ[k] L))⁻¹, ?_, δ₀, δ₀.2, by group⟩
    rw [Subgroup.mem_comap]
    have hδ₀' : SSGRoute.PTExt.galRes k K L (δ₀ : L ≃ₐ[k] L) = δw := by
      have h := hfd δ₀
      rw [hδ₀] at h
      exact h.symm
    rw [map_mul, map_inv, map_mul, hγ, hδ₀', ← hgn]
    have heq : γ * (δw * n) * (γ * δw)⁻¹ = γ * (δw * n * δw⁻¹) * γ⁻¹ := by group
    rw [heq]
    exact (inferInstance : N.Normal).conj_mem _ ((inferInstance : N.Normal).conj_mem _ hn δw) γ
  · rintro ⟨h, hh, δ, hδ, rfl⟩
    rw [Subgroup.mem_comap] at hh
    simp only [Work.SSGRoute.TPatom.concSet]
    refine ⟨SSGRoute.PTExt.galRes k K L δ, hgalδ ⟨δ, hδ⟩,
      (SSGRoute.PTExt.galRes k K L δ)⁻¹ * (γ⁻¹ * SSGRoute.PTExt.galRes k K L h * γ)
        * SSGRoute.PTExt.galRes k K L δ,
      (inferInstance : N.Normal).conj_mem _
        ((inferInstance : N.Normal).conj_mem _ hh γ⁻¹) (SSGRoute.PTExt.galRes k K L δ)⁻¹, ?_⟩
    · rw [map_mul, map_mul, hγ]
      group

/-- **Inertia descends along restriction.** -/
theorem isInertiaAt_galRes {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq' : q'.asIdeal.LiesOver q.asIdeal)
    (γ : L ≃ₐ[k] L) (hγ : SSGRoute.PTExt.IsInertiaAt q' γ) :
    SSGRoute.PTExt.IsInertiaAt (k := k) q (SSGRoute.PTExt.galRes k K L γ) := by
  haveI : FiniteDimensional K L := FiniteDimensional.right k K L
  exact SSGRoute.E9Nodes.e9_inertia_restrict k K L q q' hq' γ (SSGRoute.PTExt.galRes k K L γ)
    (fun x => (AlgEquiv.restrictNormal_commutes γ K x).symm) hγ

/-- **The decomposition group is contained in the fixing subgroup of `F` iff `F` splits
completely at the place.** -/
theorem decompK_le_fixingSubgroup_iff_split {K L : Type} [Field K] [NumberField K] [Field L]
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
lemma concentrationClause_sect_mul_mem {Γ : Type} [Group Γ] (H : Subgroup Γ) [H.Normal]
    (x : Γ) {d : Γ} (hd : d ∈ H) : sect H (x * d) = sect H x := by
  have hconj : x * d * x⁻¹ ∈ H := Subgroup.Normal.conj_mem (inferInstance : H.Normal) d hd x
  have h := sect_const H ⟨x * d * x⁻¹, hconj⟩ x
  rwa [show (x * d * x⁻¹) * x = x * d from by group] at h

/-- In a commutative group, `a * b * a⁻¹ = b`. -/
lemma concentrationClause_mul_conj_self {M : Type} [CommGroup M] (a b : M) : a * b * a⁻¹ = b := by
  rw [mul_comm a b, mul_assoc, mul_inv_cancel, mul_one]

/-- `cfunc H x d`, for `d ∈ H`, is the conjugate of `d` by the transversal defect `kappa H x`. -/
lemma concentrationClause_cfunc_eq_conj_mul {Γ : Type} [Group Γ] (H : Subgroup Γ) [H.Normal]
    (x : Γ) {d : Γ} (hd : d ∈ H) :
    cfunc H x d =
      kappa H x * (⟨x * d * x⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : H.Normal) d hd x⟩ : ↥H) *
          (kappa H x)⁻¹ := by
  apply Subtype.ext
  rw [coe_cfunc, concentrationClause_sect_mul_mem H x hd, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, kappa_coe]
  group

/-- The character `y` takes the same value on `cfunc H x d` and on the conjugate `x d x⁻¹`. -/
lemma concentrationClause_cfunc_yval {Γ : Type} [Group Γ] (H : Subgroup Γ) [H.Normal]
    {M : Type} [CommGroup M] (y : H →* M) (x : Γ) {d : Γ} (hd : d ∈ H) :
    y (cfunc H x d) =
      y (⟨x * d * x⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : H.Normal) d hd x⟩ : ↥H) := by
  rw [concentrationClause_cfunc_eq_conj_mul H x hd, map_mul, map_mul, map_inv]
  exact concentrationClause_mul_conj_self _ _

end CfuncHelpers

/-- Concentration clause: with `K1L` the level of the fixed field of `N` inside `L`, `EL` the image of the concentrated Grünwald extension (finite Galois of degree p over K1L), `y` the character of `H = N.comap galRes` killing exactly the automorphisms fixing `EL` pointwise, `q'` a prime of `L`, `d` a Frobenius at `q'` over `k` with `d ^ f ∈ H` for `f` the inertia degree of `q' ∩ K1L` over `q' ∩ k`, `u₀'` the detecting prime, `hsplit` the split-inert dictionary and `hu₀'` the prime bookkeeping, one has for every `x : Gal(L/k)`: `y (cfunc H x (d ^ f)) = 1 ↔ galRes x ∉ concSet k K w N γ`. Route: cfunc is `sect H x * d^f * (sect H x)⁻¹`, whose y-value equals that of `x d^f x⁻¹` (abelian target, normal kernel); by `hy` this is 1 iff `x d^f x⁻¹` fixes `EL`; using the mod-inertia generation at the prime `xq'` (`Work.SSGcrux.zpowers_sup_inertia_eq_decomp_proved` with `K := K1L`, conjugated, using `NK.Chebotarev.IsFrobAtConj`) and `I_{xq'} ≤ Gal(L/EL)` from `hsplit`, that is equivalent to `D_{xq'}(L/K1L) ≤ Gal(L/EL)`; by `Work.SSGcrux.PT.decompK_le_fixingSubgroup_iff_split` and `hsplit`, to `xq' ∩ K1L ≠ u₀'`; and by `hu₀'` to `galRes x ∉ concSet`. -/
theorem concentrationClause
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
    rw [Work.SSGcrux.PT.decompK_le_fixingSubgroup_iff_split (K := ↥K1L) (L := L) (F := EL)
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
    simpa using concentrationClause_cfunc_yval (N.comap (SSGRoute.PTExt.galRes k K L)) y x hdH
  rw [hstep1]
  exact hstep2.trans (hstep3.trans (hstep4.trans hstep5))


end Work.SSGcrux.PT
namespace Work.SSGcrux

open scoped NumberField Pointwise

/-- **The concentrated level-and-character data** (geometric input of the non-invariant case of
`C6`): a finite Galois level `L ⊇ K` over `k`, a place `q' | q` with `p ∤ e(q'|q)`, an element
`d ∈ D_{q'}` generating `D_{q'}` modulo `H = galRes⁻¹ N` with `d ^ f ∈ H` minimal, and a character
`y : H →* 𝔽_p` killing the normal closure of the inertia at `q'` and concentrated on the block of
`γ` (spelled `concSet k K w N γ = γ · D_w · N`). -/
theorem concentratedLevelDataExists (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (hNζ : ∀ σ ∈ N, σ ζ = ζ)
    (γ : K ≃ₐ[k] K) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
      (hcop : Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p)
      (d : ↥L ≃ₐ[k] ↥L) (f : ℕ)
      (hdH : d ^ f ∈ N.comap (SSGRoute.PTExt.galRes k K ↥L))
      (y : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)) →* Multiplicative (ZMod p)),
      d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') ∧
      0 < f ∧
      (∀ δ ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q'),
        ∃ m : ℕ, δ⁻¹ * d ^ m ∈ N.comap (SSGRoute.PTExt.galRes k K ↥L)) ∧
      (∀ m : ℕ, 0 < m → m < f → d ^ m ∉ N.comap (SSGRoute.PTExt.galRes k K ↥L)) ∧
      (∀ x : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)),
        (x : ↥L ≃ₐ[k] ↥L) ∈
          Subgroup.normalClosure {σ : ↥L ≃ₐ[k] ↥L | SSGRoute.PTExt.IsInertiaAt q' σ} →
        y x = 1) ∧
      (∀ x : ↥L ≃ₐ[k] ↥L,
        y (Work.SSGRoute.TatePoitouRoute.cfunc (N.comap (SSGRoute.PTExt.galRes k K ↥L)) x
            (⟨d ^ f, hdH⟩ : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)))) = 1 ↔
          SSGRoute.PTExt.galRes k K ↥L x ∉ Work.SSGRoute.TPatom.concSet k K w N γ) := by
  classical
  -- ## Step 0: the fixed field `K₁ = K^N`, the primes `l = q ∩ k`, `u₀ = (γ q) ∩ K₁`
  let K1 : IntermediateField k K := IntermediateField.fixedField N
  let l : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    ⟨q.asIdeal.under (NumberField.RingOfIntegers k), inferInstance,
      Ideal.under_ne_bot _ q.ne_bot⟩
  have hq_l : q.asIdeal.LiesOver l.asIdeal := Ideal.over_under q.asIdeal
  let γq : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    NK.GlobalCFT.Place.smulHeightOneSpectrum γ q
  have hγq_l : γq.asIdeal.LiesOver l.asIdeal := by
    have h : γq.asIdeal = γ • q.asIdeal := rfl
    rw [h]; infer_instance
  let u₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1) :=
    ⟨γq.asIdeal.under (NumberField.RingOfIntegers ↥K1), inferInstance,
      Ideal.under_ne_bot _ γq.ne_bot⟩
  have hu₀_l : u₀.asIdeal.LiesOver l.asIdeal := by
    haveI : γq.asIdeal.LiesOver u₀.asIdeal := Ideal.over_under γq.asIdeal
    exact Ideal.LiesOver.tower_bot γq.asIdeal u₀.asIdeal l.asIdeal
  have hpu₀ : ((p : NumberField.RingOfIntegers ↥K1) ∉ u₀.asIdeal) := by
    intro hmem
    have h1 : ((p : NumberField.RingOfIntegers k)) ∈ l.asIdeal := by
      have h2 := (Ideal.mem_of_liesOver (A := NumberField.RingOfIntegers k)
        (B := NumberField.RingOfIntegers ↥K1) (p := l.asIdeal) (P := u₀.asIdeal)
        (x := (p : NumberField.RingOfIntegers k)))
      rw [map_natCast] at h2
      exact h2.mpr hmem
    have h3 : ((p : NumberField.RingOfIntegers K)) ∈ q.asIdeal := by
      rw [show l.asIdeal = q.asIdeal.under (NumberField.RingOfIntegers k) from rfl] at h1
      rw [Ideal.mem_under] at h1
      rwa [map_natCast] at h1
    exact hpq h3
  -- ## Step 1: the Grünwald–Wang concentrated extension `E/K₁`
  let S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1)) :=
    (NK.GlobalCFT.Place.primesOverFinite l).erase u₀
  have hqS : u₀ ∉ S := by simp [S]
  obtain ⟨E, hnfE, hfdE, hgalE, hrankE, hsplitE, hinertE⟩ :=
    Work.SSGRoute.Sha2Lib.exists_cyclic_p_level_split_inert p ↥K1 Ω S u₀ hqS hpu₀
  -- ## Step 2: the level `L = normalClosure k (K ⊔ E)` and its instances
  let Kf : IntermediateField k Ω := (IsScalarTower.toAlgHom k K Ω).fieldRange
  let E' : IntermediateField k Ω := E.restrictScalars k
  let MM : IntermediateField k Ω := Kf ⊔ E'
  let Nc : IntermediateField k Ω := IntermediateField.normalClosure k ↥MM Ω
  have hKfM : Kf ≤ MM := le_sup_left
  have hMleN : MM ≤ Nc := IntermediateField.le_normalClosure MM
  have hKM : ∀ x : K, algebraMap K Ω x ∈ Nc := fun x =>
    hMleN (hKfM (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩))
  let L : IntermediateField K Ω := Nc.toSubfield.toIntermediateField hKM
  haveI hfdKf : FiniteDimensional k ↥Kf :=
    (AlgHom.equivFieldRange (IsScalarTower.toAlgHom k K Ω)).toLinearEquiv.finiteDimensional
  haveI hfdE' : FiniteDimensional k ↥E' := FiniteDimensional.trans k ↥K1 ↥E
  haveI hfdMM : FiniteDimensional k ↥MM := inferInstance
  haveI hAlgMM : Algebra.IsAlgebraic k ↥MM := Algebra.IsAlgebraic.of_finite k ↥MM
  haveI hNC : IsNormalClosure k ↥MM ↥Nc :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure
      (fun x => IsAlgClosed.splits ((minpoly k x).map (algebraMap k Ω)))
  haveI hNcnorm : Normal k ↥Nc := IsNormalClosure.normal (K := ↥MM)
  haveI hLnorm : Normal k ↥L := hNcnorm
  haveI hfdL : FiniteDimensional k ↥L := normalClosure.is_finiteDimensional k ↥MM Ω
  haveI hnfL : NumberField ↥L := NumberField.of_module_finite k ↥L
  haveI hsepL : Algebra.IsSeparable k ↥L := Algebra.IsSeparable.of_integral k ↥L
  haveI hgalL : IsGalois k ↥L := ⟨⟩
  haveI hfdKL : FiniteDimensional K ↥L := Module.Finite.of_restrictScalars_finite k K ↥L
  haveI hgalKL : IsGalois K ↥L := IsGalois.tower_top_of_isGalois k K ↥L
  -- ## Step 3: a place `q'` of `L` over `q`
  obtain ⟨q', hq'lies⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := ↥L) q
  have hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w := by
    rw [hwq]; exact NK.GlobalCFT.Place.liesOver_ofFinite hq'lies
  -- ## Step 4: `E` viewed inside `L` over `K₁`, and the character `y : H →* Multiplicative (ZMod p)`
  let Lk : IntermediateField k Ω := L.restrictScalars k
  let K1f : IntermediateField k Ω := K1.map (IsScalarTower.toAlgHom k K Ω)
  have hK1f_le_E' : K1f ≤ E' := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map (S := K1)).mp hx
    rw [IntermediateField.mem_restrictScalars]
    exact E.algebraMap_mem ⟨y, hy⟩
  have hMM_le_L : MM ≤ Lk := fun x hx => hMleN hx
  have hE'_le_L : E' ≤ Lk := le_trans le_sup_right hMM_le_L
  haveI hSTL : IsScalarTower k ↥L Ω :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply k K Ω, IsScalarTower.algebraMap_apply k K ↥L,
        IsScalarTower.algebraMap_apply K ↥L Ω])
  let K1L : IntermediateField k ↥L := K1.map (IsScalarTower.toAlgHom k K ↥L)
  let E0 : IntermediateField k ↥L := E'.comap (IsScalarTower.toAlgHom k ↥L Ω)
  have hK1L_le_E0 : K1L ≤ E0 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map (S := K1)).mp hx
    exact hK1f_le_E' ((IntermediateField.mem_map (S := K1)).mpr ⟨y, hy, rfl⟩)
  let EL : IntermediateField ↥K1L ↥L := IntermediateField.extendScalars hK1L_le_E0
  haveI hfdK1 : FiniteDimensional k ↥K1 :=
    Module.Finite.of_injective (IntermediateField.val K1).toLinearMap
      (IntermediateField.val K1).injective
  let eK1 : ↥K1 ≃ₐ[k] ↥K1L :=
    IntermediateField.equivMap K1 (IsScalarTower.toAlgHom k K ↥L)
  let eK1O : NumberField.RingOfIntegers ↥K1 ≃ₐ[NumberField.RingOfIntegers k]
      NumberField.RingOfIntegers ↥K1L := NumberField.RingOfIntegers.mapAlgEquiv eK1
  have hcompatK1O' : (eK1O : NumberField.RingOfIntegers ↥K1 →+*
      NumberField.RingOfIntegers ↥K1L).comp (algebraMap (NumberField.RingOfIntegers k)
        (NumberField.RingOfIntegers ↥K1)) = algebraMap (NumberField.RingOfIntegers k)
          (NumberField.RingOfIntegers ↥K1L) :=
    RingHom.ext fun c => eK1O.commutes c
  have hkeyO : ∀ x : NumberField.RingOfIntegers ↥K1,
      algebraMap (NumberField.RingOfIntegers ↥K1L) (NumberField.RingOfIntegers ↥L) (eK1O x)
        = algebraMap (NumberField.RingOfIntegers ↥K1) (NumberField.RingOfIntegers ↥L) x := by
    intro x
    apply NumberField.RingOfIntegers.coe_injective
    rw [← IsScalarTower.algebraMap_apply (R := NumberField.RingOfIntegers ↥K1L)
          (S := NumberField.RingOfIntegers ↥L) (A := ↥L) (eK1O x),
        ← IsScalarTower.algebraMap_apply (R := NumberField.RingOfIntegers ↥K1)
          (S := NumberField.RingOfIntegers ↥L) (A := ↥L) x]
    change (((eK1O x : NumberField.RingOfIntegers ↥K1L) : ↥K1L) : ↥L)
        = algebraMap K ↥L (((x : NumberField.RingOfIntegers ↥K1) : ↥K1) : K)
    rw [show ((eK1O x : NumberField.RingOfIntegers ↥K1L) : ↥K1L) = eK1 (x : ↥K1) from
      NumberField.RingOfIntegers.mapRingHom_apply (f := (eK1 : ↥K1 →+* ↥K1L)) x]
    rw [show (eK1 (x : ↥K1) : ↥L)
          = algebraMap K ↥L (((x : NumberField.RingOfIntegers ↥K1) : ↥K1) : K) from
        IntermediateField.coe_equivMap_apply (L := K1)
          (f := IsScalarTower.toAlgHom k K ↥L) (x : ↥K1)]
  haveI hfdK1L : FiniteDimensional k ↥K1L := eK1.toLinearEquiv.finiteDimensional
  haveI hnfK1L : NumberField ↥K1L := NumberField.of_module_finite k ↥K1L
  haveI hgalK1LL : IsGalois ↥K1L ↥L := inferInstance
  haveI hfinK1LL : FiniteDimensional ↥K1L ↥L := by
    haveI : IsScalarTower k ↥K1L ↥L := inferInstance
    exact Module.Finite.of_restrictScalars_finite k ↥K1L ↥L
  haveI hfdEL : FiniteDimensional ↥K1L ↥EL :=
    Module.Finite.of_injective EL.val.toLinearMap EL.val.injective
  have hELmem : ∀ (y : ↥L), y ∈ EL ↔ (y : Ω) ∈ E := by
    intro y
    rw [show y ∈ EL ↔ y ∈ E0 from (IntermediateField.mem_extendScalars (h := hK1L_le_E0))]
    rw [show y ∈ E0 ↔ (IsScalarTower.toAlgHom k ↥L Ω) y ∈ E' from Iff.rfl]
    rw [show (IsScalarTower.toAlgHom k ↥L Ω) y = (y : Ω) from rfl]
    rw [IntermediateField.mem_restrictScalars]
  let eEL : ↥E ≃ₐ[k] ↥EL :=
    { toFun := fun x => Subtype.mk
        (Subtype.mk x.1 (hE'_le_L ((IntermediateField.mem_restrictScalars (K := k) (E := E)).mpr x.2)))
        ((hELmem (Subtype.mk x.1
          (hE'_le_L ((IntermediateField.mem_restrictScalars (K := k) (E := E)).mpr x.2)))).mpr x.2)
      invFun := fun y => Subtype.mk (y.1.1) ((hELmem y.1).mp y.2)
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext (Subtype.ext rfl)
      map_mul' := fun x y => Subtype.ext (Subtype.ext rfl)
      map_add' := fun x y => Subtype.ext (Subtype.ext rfl)
      commutes' := fun c => Subtype.ext (Subtype.ext rfl) }
  have hcompatEL : ∀ (a : ↥K1) (y : ↥E), eEL (a • y) = eK1 a • eEL y := by
    intro a y
    apply Subtype.ext
    apply Subtype.ext
    simp only [Algebra.smul_def, IntermediateField.coe_mul, IntermediateField.coe_algebraMap_apply,
      map_mul]
    rw [show (↑↑(eEL (algebraMap ↥K1 ↥E a)) : Ω) = (↑((algebraMap ↥K1 ↥E) a) : Ω) from rfl]
    rw [show (↑((algebraMap ↥K1 ↥E) a) : Ω) = (algebraMap ↥K1 Ω) a from rfl]
    rw [show (↑((algebraMap ↥K1L ↥L) (eK1 a)) : Ω) = (algebraMap ↥K1L Ω) (eK1 a) from rfl]
    have hkey : (algebraMap ↥K1L Ω) (eK1 a) = (algebraMap ↥K1 Ω) a := by
      rw [show (algebraMap ↥K1L Ω) (eK1 a) = ((eK1 a : ↥K1L) : ↥L).1 from rfl]
      rw [show ((eK1 a : ↥K1L) : ↥L) = ((IsScalarTower.toAlgHom k K ↥L) a : ↥L) from by
        rw [show (eK1 a : ↥K1L) = IntermediateField.equivMap K1
          (IsScalarTower.toAlgHom k K ↥L) a from rfl, IntermediateField.coe_equivMap_apply]]
      rw [show ((IsScalarTower.toAlgHom k K ↥L) a : ↥L) = algebraMap K ↥L ((a : ↥K1) : K) from rfl]
      rw [IntermediateField.coe_algebraMap_apply]
      rw [IsScalarTower.algebraMap_apply ↥K1 K Ω a]
      rw [show (algebraMap ↥K1 K) a = ((a : ↥K1) : K) from rfl]
    rw [hkey]
  haveI hgalEL : IsGalois ↥K1L ↥EL :=
    IsGalois.of_equiv_equiv (F := ↥K1) (E := ↥E) (f := (eK1 : ↥K1 ≃+* ↥K1L)) (g := eEL) (by
      apply RingHom.ext
      intro x
      apply Subtype.ext
      apply Subtype.ext
      simp only [IntermediateField.coe_algebraMap_apply, IntermediateField.algebraMap_apply,
        IntermediateField.coe_equivMap_apply, eEL]
      rfl)
  have hrankEL : Module.finrank ↥K1L ↥EL = p := by
    rw [← hrankE]
    exact (Algebra.finrank_eq_of_equiv_equiv (eK1 : ↥K1 ≃+* ↥K1L) eEL (by
      apply RingHom.ext
      intro x
      apply Subtype.ext
      apply Subtype.ext
      simp only [IntermediateField.coe_algebraMap_apply, IntermediateField.algebraMap_apply,
        IntermediateField.coe_equivMap_apply, eEL]
      rfl)).symm
  obtain ⟨χ, hχker⟩ :=
    Work.SSGcrux.exists_char_ker_fixingSubgroup (K := ↥K1L) (L := ↥L) EL p hrankEL
  -- ## Step 5: `H = galRes⁻¹ N = Gal(L/K₁)` and the character `y : H →* Multiplicative (ZMod p)`
  have hK1fix : K1.fixingSubgroup = N := IntermediateField.fixingSubgroup_fixedField N
  have hHmem : ∀ σ : ↥L ≃ₐ[k] ↥L,
      SSGRoute.PTExt.galRes k K ↥L σ ∈ N ↔ σ ∈ K1L.fixingSubgroup := by
    intro σ
    rw [← hK1fix, IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map (S := K1)).mp hx
      show σ (algebraMap K ↥L y) = algebraMap K ↥L y
      rw [show σ (algebraMap K ↥L y) = algebraMap K ↥L (SSGRoute.PTExt.galRes k K ↥L σ y)
        from (AlgEquiv.restrictNormal_commutes σ K y).symm]
      rw [h y hy]
    · intro h y hy
      have hx : (IsScalarTower.toAlgHom k K ↥L) y ∈ K1L :=
        (IntermediateField.mem_map (S := K1)).mpr ⟨y, hy, rfl⟩
      have hfix := h _ hx
      rw [show (IsScalarTower.toAlgHom k K ↥L) y = algebraMap K ↥L y from rfl] at hfix
      rw [show σ (algebraMap K ↥L y) = algebraMap K ↥L (SSGRoute.PTExt.galRes k K ↥L σ y)
        from (AlgEquiv.restrictNormal_commutes σ K y).symm] at hfix
      exact (algebraMap K ↥L).injective hfix
  have hH : N.comap (SSGRoute.PTExt.galRes k K ↥L) = K1L.fixingSubgroup := by
    ext σ
    rw [Subgroup.mem_comap]
    exact hHmem σ
  let y : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)) →* Multiplicative (ZMod p) :=
    χ.comp (MulEquiv.toMonoidHom
      ((MulEquiv.subgroupCongr hH).trans (IntermediateField.fixingSubgroupEquiv K1L)))
  have hy_iff : ∀ (σ : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L))),
      y σ = 1 ↔ ∀ x : ↥L, x ∈ EL → (σ : ↥L ≃ₐ[k] ↥L) x = x := by
    intro σ
    have hcoe : (((MulEquiv.subgroupCongr hH).trans
        (IntermediateField.fixingSubgroupEquiv K1L)) σ : ↥L → ↥L)
          = ⇑(σ : ↥L ≃ₐ[k] ↥L) := rfl
    rw [show y σ = χ (((MulEquiv.subgroupCongr hH).trans
        (IntermediateField.fixingSubgroupEquiv K1L)) σ) from rfl,
      ← MonoidHom.mem_ker, hχker, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx; rw [← hcoe]; exact h x hx
    · intro h x hx; rw [hcoe]; exact h x hx
  -- ## Step 6: the prime `u = q ∩ K₁` of `K₁` over `l`, and its unramifiedness over `k`
  let u : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1) :=
    ⟨q.asIdeal.under (NumberField.RingOfIntegers ↥K1), inferInstance,
      Ideal.under_ne_bot _ q.ne_bot⟩
  have hq_u : q.asIdeal.LiesOver u.asIdeal := Ideal.over_under q.asIdeal
  have hu_l : u.asIdeal.LiesOver l.asIdeal := by
    have h : l.asIdeal = u.asIdeal.under (NumberField.RingOfIntegers k) := by
      show q.asIdeal.under (NumberField.RingOfIntegers k) =
        (q.asIdeal.under (NumberField.RingOfIntegers ↥K1)).under (NumberField.RingOfIntegers k)
      rw [Ideal.under_under]
    exact ⟨h⟩
  haveI hgalK1 : IsGalois k ↥K1 := inferInstance
  have hu_inertia_bot : Ideal.inertia (↥K1 ≃ₐ[k] ↥K1) u.asIdeal = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro τ hτ
    exact Work.SSGRoute.TPatom.fixedField_inertia_eq_bot N q u hq_u hNI τ
      ((Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia (k := k) (K := ↥K1) u τ).mpr hτ)
  have hu_unr : u.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    haveI : u.asIdeal.LiesOver l.asIdeal := hu_l
    haveI : u.asIdeal.IsPrime := u.isPrime
    haveI : l.asIdeal.IsPrime := l.isPrime
    exact (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
      (F := k) (K := ↥K1) l.asIdeal u.asIdeal).mp hu_inertia_bot
  -- A2: *every* prime of `K₁` over `l` is unramified over `k` (proved helper)
  have hK1unr_all : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1),
      𝔭.asIdeal.LiesOver l.asIdeal →
        𝔭.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    intro 𝔭 h𝔭
    exact Work.SSGate.fixedField_ramificationIdx_eq_one N q hNI 𝔭 (by
      rwa [show q.asIdeal.under (NumberField.RingOfIntegers k) = l.asIdeal from rfl])
  -- ## Step 7: an arithmetic Frobenius `d` at `q'` for `L/k`
  have hq'l : q'.asIdeal.LiesOver l.asIdeal := by
    refine ⟨?_⟩
    rw [show l.asIdeal = q.asIdeal.under (NumberField.RingOfIntegers k) from rfl, hq'lies.over]
    exact Ideal.under_under q'.asIdeal
  obtain ⟨d, hdFrob⟩ := NK.Chebotarev.exists_isFrobAt (K := k) (L := ↥L) l q' hq'l
  have hdD : d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') := by
    exact (Work.SSGcrux.mem_decompK_ofFinite_iff q' d).mpr (by
      apply IsDedekindDomain.HeightOneSpectrum.ext
      rw [← Work.SSGcrux.smul_primeIdeal_eq_smulHeightOneSpectrum' d q',
        NK.Chebotarev.smul_primeIdeal_asIdeal]
      exact NK.Chebotarev.IsFrobAtStabilizes hdFrob)
  -- ## Step 8: `q1 = q' ∩ K₁L`, its unramifiedness over `k`, and the Frobenius bookkeeping
  let q1 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1L) :=
    ⟨q'.asIdeal.under (NumberField.RingOfIntegers ↥K1L), inferInstance,
      Ideal.under_ne_bot _ q'.ne_bot⟩
  have hq1_l : q1.asIdeal.LiesOver l.asIdeal := by
    refine ⟨?_⟩
    rw [show l.asIdeal = q.asIdeal.under (NumberField.RingOfIntegers k) from rfl, hq'lies.over]
    exact Ideal.under_under q'.asIdeal
  have hu_eq : u.asIdeal = Ideal.under (NumberField.RingOfIntegers ↥K1) q'.asIdeal := by
    rw [show u.asIdeal = q.asIdeal.under (NumberField.RingOfIntegers ↥K1) from rfl,
      hq'lies.over, Ideal.under_under]
  have hcomap1 : Ideal.comap eK1O q1.asIdeal = u.asIdeal := by
    apply Ideal.ext
    intro x
    rw [Ideal.mem_comap]
    show eK1O x ∈ q1.asIdeal ↔ x ∈ u.asIdeal
    rw [show q1.asIdeal = Ideal.under (NumberField.RingOfIntegers ↥K1L) q'.asIdeal from rfl,
      Ideal.mem_under, hkeyO x, hu_eq, Ideal.mem_under]
  have hq1_unr : q1.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    haveI : q1.asIdeal.LiesOver l.asIdeal := hq1_l
    haveI : q1.asIdeal.IsPrime := q1.isPrime
    haveI : l.asIdeal.IsPrime := l.isPrime
    rw [← Work.SSGRoute.Sha2Lib.ramificationIdx_comap_algEquiv ↥K1 ↥K1L eK1O l
      q1.asIdeal, hcomap1]
    exact hu_unr
  haveI hgalK1L : IsGalois k ↥K1L := IsGalois.of_algEquiv eK1
  have hd1 : NK.Chebotarev.IsFrobAt (K := k) (L := ↥K1L) q1
      (AlgEquiv.restrictNormalHom ↥K1L d) :=
    NK.Chebotarev.IsFrobAtRestrictNormalHom (K := k) (M := ↥L) K1L hq'l hdFrob
  have hcyc : SSGRoute.PTExt.decompK (k := k) (K := ↥K1L) (NK.GlobalCFT.Place.ofFinite q1)
      = Subgroup.zpowers (AlgEquiv.restrictNormalHom ↥K1L d) :=
    Work.SSGRoute.Sha2Lib.stabilizer_ofFinite_eq_zpowers_of_isFrobAt (K := k) (L := ↥K1L)
      q1 hq1_unr (AlgEquiv.restrictNormalHom ↥K1L d) hd1
  let f : ℕ := orderOf (AlgEquiv.restrictNormalHom ↥K1L d)
  have hfpos : 0 < f := orderOf_pos _
  have hd1f : (AlgEquiv.restrictNormalHom ↥K1L d) ^ f = 1 := pow_orderOf_eq_one _
  have hker : (AlgEquiv.restrictNormalHom ↥K1L).ker = N.comap (SSGRoute.PTExt.galRes k K ↥L) := by
    rw [hH, IntermediateField.restrictNormalHom_ker]
  have hmemK : ∀ δ : ↥L ≃ₐ[k] ↥L,
      δ ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') →
      AlgEquiv.restrictNormalHom ↥K1L δ ∈ Subgroup.zpowers (AlgEquiv.restrictNormalHom ↥K1L d) := by
    intro δ hδ
    rw [← hcyc, Work.SSGcrux.mem_decompK_ofFinite_iff]
    have hδ' : NK.GlobalCFT.Place.smulHeightOneSpectrum δ q' = q' :=
      (Work.SSGcrux.mem_decompK_ofFinite_iff q' δ).mp hδ
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
    have hnat := Work.SSGRoute.Sha2Lib.under_smul_heightOneSpectrum (k := k) (K := ↥K1L)
      (L := ↥L) δ q'
    have h2 : Ideal.map (NK.GlobalCFT.Place.ringOfIntegersEquiv (AlgEquiv.restrictNormalHom ↥K1L δ))
        (Ideal.under (NumberField.RingOfIntegers ↥K1L) q'.asIdeal)
        = Ideal.under (NumberField.RingOfIntegers ↥K1L)
            (NK.GlobalCFT.Place.smulHeightOneSpectrum δ q').asIdeal := hnat.symm
    rw [show q1.asIdeal = Ideal.under (NumberField.RingOfIntegers ↥K1L) q'.asIdeal from rfl,
      h2, hδ']
  have hdgen : ∀ δ ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L)
      (NK.GlobalCFT.Place.ofFinite q'),
      ∃ m : ℕ, δ⁻¹ * d ^ m ∈ N.comap (SSGRoute.PTExt.galRes k K ↥L) := by
    intro δ hδ
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hmemK δ hδ)
    refine ⟨(n % (f : ℤ)).toNat, ?_⟩
    have hm : (((n % (f : ℤ)).toNat : ℕ) : ℤ) = n % (f : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg n (by exact_mod_cast hfpos.ne'))
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, map_pow, ← hn]
    rw [← zpow_natCast, hm, ← zpow_eq_zpow_emod' n hd1f]
    group
  have hfmin : ∀ m : ℕ, 0 < m → m < f →
      d ^ m ∉ N.comap (SSGRoute.PTExt.galRes k K ↥L) := by
    intro m hm0 hmf hmem
    rw [← hker, MonoidHom.mem_ker, map_pow] at hmem
    have hdvd : f ∣ m := by
      rw [show f = orderOf (AlgEquiv.restrictNormalHom ↥K1L d) from rfl]
      exact orderOf_dvd_iff_pow_eq_one.mpr hmem
    exact absurd (Nat.le_of_dvd hm0 hdvd) (Nat.not_le.mpr hmf)
  have hdH : d ^ f ∈ N.comap (SSGRoute.PTExt.galRes k K ↥L) := by
    rw [← hker, MonoidHom.mem_ker, map_pow, hd1f]
  -- ## Step 9: the inertia degree of `q1` over `k` is `f`
  have hfdeg : f = q1.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    rw [show f = orderOf (AlgEquiv.restrictNormalHom ↥K1L d) from rfl]
    exact NK.Chebotarev.IsFrobAtOrderOfEqInertiaDeg (p := l) (P := q1)
      hq1_l hq1_unr hd1
  -- ## Step 10: the detecting prime `u₀'` and the split/inert dictionary
  have hmapPrime : (Ideal.map (eK1O : NumberField.RingOfIntegers ↥K1 →+*
      NumberField.RingOfIntegers ↥K1L) u₀.asIdeal).IsPrime :=
    Ideal.map_isPrime_of_surjective (f := (eK1O : NumberField.RingOfIntegers ↥K1 →+*
      NumberField.RingOfIntegers ↥K1L)) eK1O.surjective (by
        intro x hx
        rw [RingHom.mem_ker] at hx
        have hx0 : x = 0 := eK1O.injective (by simpa using hx)
        rw [hx0]
        exact u₀.asIdeal.zero_mem)
  have hmapNe : Ideal.map (eK1O : NumberField.RingOfIntegers ↥K1 →+*
      NumberField.RingOfIntegers ↥K1L) u₀.asIdeal ≠ ⊥ := by
    intro hbot
    exact u₀.ne_bot ((Ideal.map_eq_bot_iff_of_injective (f := (eK1O :
      NumberField.RingOfIntegers ↥K1 →+* NumberField.RingOfIntegers ↥K1L))
      eK1O.injective).mp hbot)
  let u₀' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1L) :=
    ⟨Ideal.map (eK1O : NumberField.RingOfIntegers ↥K1 →+* NumberField.RingOfIntegers ↥K1L)
        u₀.asIdeal, hmapPrime, hmapNe⟩
  have hu₀'eq : u₀'.asIdeal = Ideal.map (eK1O : NumberField.RingOfIntegers ↥K1 →+*
      NumberField.RingOfIntegers ↥K1L) u₀.asIdeal := rfl
  have hK1unr_all_L : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1L),
      𝔭.asIdeal.LiesOver l.asIdeal →
        𝔭.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    intro 𝔭 h𝔭
    haveI : 𝔭.asIdeal.LiesOver l.asIdeal := h𝔭
    haveI : 𝔭.asIdeal.IsPrime := 𝔭.isPrime
    haveI : l.asIdeal.IsPrime := l.isPrime
    let 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1) :=
      IsDedekindDomain.HeightOneSpectrum.comap (eK1O : NumberField.RingOfIntegers ↥K1 →+*
        NumberField.RingOfIntegers ↥K1L) eK1O.surjective 𝔭
    have h𝔮 : 𝔮.asIdeal.LiesOver l.asIdeal := by
      refine Ideal.LiesOver.mk ?_
      rw [h𝔭.over, show 𝔮.asIdeal = Ideal.comap (eK1O : NumberField.RingOfIntegers ↥K1 →+*
        NumberField.RingOfIntegers ↥K1L) 𝔭.asIdeal from rfl]
      simp only [Ideal.under_def, Ideal.comap_comap, hcompatK1O']
    rw [← Work.SSGRoute.Sha2Lib.ramificationIdx_comap_algEquiv ↥K1 ↥K1L eK1O l 𝔭.asIdeal]
    exact hK1unr_all 𝔮 h𝔮
  have hsplit : ∀ p' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1L),
      p'.asIdeal.LiesOver l.asIdeal →
      ∀ 𝔮' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥EL),
        𝔮'.asIdeal.LiesOver p'.asIdeal →
          𝔮'.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥K1L) = 1 ∧
          (𝔮'.asIdeal.inertiaDeg (NumberField.RingOfIntegers ↥K1L) = 1 ↔ p' ≠ u₀') := by
    classical
    have hSu : ∀ u' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1),
        u'.asIdeal.LiesOver l.asIdeal → u' ≠ u₀ → u' ∈ S := by
      intro u' hu' hne
      simp only [S, Finset.mem_erase, NK.GlobalCFT.Place.mem_primesOverFinite]
      exact ⟨hne, hu'⟩
    exact Work.SSGRoute.TPatom.EL_split_inert_dictionary (k := k) (K1 := ↥K1) (K1L := ↥K1L)
      (L := ↥L) (E := ↥E) (EL := ↥EL) p eK1 eEL hcompatEL l u₀ u₀' (by rw [hu₀'eq])
      hu₀_l S hSu hsplitE hinertE
  have hl_eq : l.asIdeal = q'.asIdeal.under (NumberField.RingOfIntegers k) := by
    rw [show l.asIdeal = q.asIdeal.under (NumberField.RingOfIntegers k) from rfl, hq'lies.over,
      Ideal.under_under]
  have hsplit6 : ∀ p' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1L),
      p'.asIdeal.LiesOver (q'.asIdeal.under (NumberField.RingOfIntegers k)) →
      ∀ 𝔮' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥EL),
        𝔮'.asIdeal.LiesOver p'.asIdeal →
          𝔮'.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥K1L) = 1 ∧
          (𝔮'.asIdeal.inertiaDeg (NumberField.RingOfIntegers ↥K1L) = 1 ↔ p' ≠ u₀') := by
    intro p' hp' 𝔮' h𝔮'
    exact hsplit p' (Ideal.LiesOver.mk (by rw [hl_eq, hp'.over])) 𝔮' h𝔮'
  -- ## Step 11: `L/K` is unramified at `q'` (giving `hcop`)
  have hNcEq : L.restrictScalars k = IntermediateField.normalClosure k ↥MM Ω := by
    ext x
    exact Iff.rfl
  have hIbot : Ideal.inertia (↥L ≃ₐ[K] ↥L) q'.asIdeal = ⊥ := by
    haveI hNormL : Normal k ↥L := IsGalois.to_normal
    -- The generation of `L` over `k` by the image of `K` and the conjugates of `MM ∩ L`.
    have hgen0 := Work.SSGRoute.Sha2Lib.normalClosureEqTop (k := k) (K := K) (Ω := Ω) MM L
      hMM_le_L hNcEq
    -- `val`, the inclusion of `↥L` into `Ω`, composed with the inclusion of `K`, is the
    -- inclusion of `K` into `Ω`.
    have hval : (IsScalarTower.toAlgHom k ↥L Ω).comp (IsScalarTower.toAlgHom k K ↥L)
        = IsScalarTower.toAlgHom k K Ω :=
      AlgHom.ext fun x => IsScalarTower.algebraMap_apply K ↥L Ω x
    -- `EL`, viewed over `k`, is `E' ∩ ↥L`
    have hE0 : EL.restrictScalars k = E'.comap (IsScalarTower.toAlgHom k ↥L Ω) :=
      IntermediateField.extendScalars_restrictScalars hK1L_le_E0
    have hLk : Lk = (IsScalarTower.toAlgHom k ↥L Ω).fieldRange := by
      ext x
      exact ⟨fun hx => AlgHom.mem_fieldRange.mpr ⟨⟨x, hx⟩, rfl⟩,
        fun hx => (AlgHom.mem_fieldRange.mp hx).elim fun y hy => hy ▸ y.2⟩
    have hMMle : MM ≤ (IsScalarTower.toAlgHom k ↥L Ω).fieldRange := hLk ▸ hMM_le_L
    have hE'le : E' ≤ (IsScalarTower.toAlgHom k ↥L Ω).fieldRange := hLk ▸ hE'_le_L
    -- `MM ∩ ↥L` is `K · E` inside `↥L`
    have hcomap : MM.comap (IsScalarTower.toAlgHom k ↥L Ω)
        = (IsScalarTower.toAlgHom k K ↥L).fieldRange ⊔ EL.restrictScalars k := by
      refine IntermediateField.map_injective (IsScalarTower.toAlgHom k ↥L Ω) ?_
      rw [IntermediateField.map_comap_eq_self hMMle, IntermediateField.map_sup, hE0,
        IntermediateField.map_comap_eq_self hE'le, AlgHom.map_fieldRange, hval]
    -- the generation hypothesis in the shape required by the concentrated-level lemma
    have hgen : (⊤ : IntermediateField k ↥L) ≤ (IsScalarTower.toAlgHom k K ↥L).fieldRange ⊔
        K1L ⊔ ⨆ τ : (↥L ≃ₐ[k] ↥L), (EL.restrictScalars k).map (τ : ↥L →ₐ[k] ↥L) := by
      haveI hgalA : IsGalois k ↥((IsScalarTower.toAlgHom k K ↥L).fieldRange) :=
        IsGalois.of_algEquiv (AlgHom.equivFieldRange (IsScalarTower.toAlgHom k K ↥L))
      have hnormA : Normal k ↥((IsScalarTower.toAlgHom k K ↥L).fieldRange) := IsGalois.to_normal
      have hAmap : ∀ τ : (↥L ≃ₐ[k] ↥L),
          ((IsScalarTower.toAlgHom k K ↥L).fieldRange).map (τ : ↥L →ₐ[k] ↥L)
            = (IsScalarTower.toAlgHom k K ↥L).fieldRange :=
        fun τ => (IntermediateField.normal_iff_forall_map_eq.mp hnormA) τ
      rw [show (⊤ : IntermediateField k ↥L) = (IsScalarTower.toAlgHom k K ↥L).fieldRange ⊔
          ⨆ τ : (↥L ≃ₐ[k] ↥L),
            (MM.comap (IsScalarTower.toAlgHom k ↥L Ω)).map (τ : ↥L →ₐ[k] ↥L)
          from hgen0.symm]
      refine sup_le (le_trans le_sup_left le_sup_left) ?_
      rw [iSup_le_iff]
      intro τ
      refine le_trans (IntermediateField.map_mono (τ : ↥L →ₐ[k] ↥L) hcomap.le) ?_
      rw [IntermediateField.map_sup, hAmap τ]
      refine sup_le (le_trans le_sup_left le_sup_left) ?_
      exact le_trans (le_iSup (fun σ : (↥L ≃ₐ[k] ↥L) =>
        (EL.restrictScalars k).map (σ : ↥L →ₐ[k] ↥L)) τ) le_sup_right
    exact Work.SSGate.inertia_eq_bot_of_concentrated_level (k := k) (K := K) (L := ↥L)
      l K1L EL hgen q q' hq'lies hq'l hK1unr_all_L
      (fun 𝔭 h𝔭 𝔮 h𝔮 => (hsplit 𝔭 h𝔭 𝔮 h𝔮).1)
  have hcop : Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p :=
    Work.SSGRoute.Sha2Lib.coprime_ramificationIdx'_of_inertia_eq_bot (k := k) p q q' hq'lies hIbot
  -- ## Step 12: the `concSet` dictionary for the detecting prime
  have hu₀'_dict : ∀ x : ↥L ≃ₐ[k] ↥L,
      ((NK.GlobalCFT.Place.smulHeightOneSpectrum x q').asIdeal.under
          (NumberField.RingOfIntegers ↥K1L) = u₀'.asIdeal ↔
        SSGRoute.PTExt.galRes k K ↥L x ∈ Work.SSGRoute.TPatom.concSet k K w N γ) := by
    obtain ⟨σ₀, hσ₀⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) ↥L γ
    obtain ⟨u₀'', hu₀''eq, hu₀''dict⟩ :=
      Work.SSGcrux.under_eq_iff_mem_concSet (N := N) (K1 := K1) (K1L := K1L)
        eK1 (fun x => IntermediateField.coe_equivMap_apply (L := K1)
          (f := IsScalarTower.toAlgHom k K ↥L) x) hH w q hwq γ q' hq'lies σ₀ hσ₀
    have heq : u₀'' = u₀' := by
      apply IsDedekindDomain.HeightOneSpectrum.ext
      rw [hu₀''eq, show u₀'.asIdeal = Ideal.map
        ((NumberField.RingOfIntegers.mapAlgEquiv eK1) : NumberField.RingOfIntegers ↥K1 →+*
          NumberField.RingOfIntegers ↥K1L) u₀.asIdeal from hu₀'eq]
    intro x
    rw [← heq]
    exact hu₀''dict x
  -- ## Step 13: the inertia clause
  have hcl5 : ∀ x : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)),
      (x : ↥L ≃ₐ[k] ↥L) ∈
        Subgroup.normalClosure {σ : ↥L ≃ₐ[k] ↥L | SSGRoute.PTExt.IsInertiaAt q' σ} →
      y x = 1 := by
    -- every prime of `K₁L` over `q' ∩ k` is unramified over `k`
    have hunrK1L : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1L),
        𝔭.asIdeal.LiesOver (q'.asIdeal.under (NumberField.RingOfIntegers k)) →
        𝔭.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 :=
      fun 𝔭 h𝔭 => hK1unr_all_L 𝔭 (Ideal.LiesOver.mk (by rw [hl_eq, h𝔭.over]))
    -- `EL/K₁L` is unramified at every prime over `q' ∩ k`
    have hunrEL : ∀ p' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1L),
        p'.asIdeal.LiesOver (q'.asIdeal.under (NumberField.RingOfIntegers k)) →
        ∀ 𝔮' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥EL),
          𝔮'.asIdeal.LiesOver p'.asIdeal →
            𝔮'.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥K1L) = 1 :=
      fun p' hp' 𝔮' h𝔮' => (hsplit6 p' hp' 𝔮' h𝔮').1
    intro x hx
    rw [hy_iff x]
    intro z hz
    exact Work.SSGcrux.normalClosure_inertia_le_fixingSubgroup (k := k) (K1 := ↥K1L) (L := ↥L)
      EL q' hunrK1L hunrEL x hx z hz
  -- ## Step 14: the concentration clause
  have hcl6 : ∀ x : ↥L ≃ₐ[k] ↥L,
      y (Work.SSGRoute.TatePoitouRoute.cfunc (N.comap (SSGRoute.PTExt.galRes k K ↥L)) x
          (⟨d ^ f, hdH⟩ : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)))) = 1 ↔
        SSGRoute.PTExt.galRes k K ↥L x ∉ Work.SSGRoute.TPatom.concSet k K w N γ :=
    Work.SSGcrux.PT.concentrationClause (k := k) (K := K) (L := ↥L) p N K1L EL
      hH hgalEL hgalK1LL y hy_iff q' d f hdFrob hdH hfdeg w γ u₀' hu₀'_dict hsplit6
  exact ⟨L, hnfL, hfdL, hgalL, q', hq', hcop, d, f, hdH, y,
    hdD, hfpos, hdgen, hfmin, hcl5, hcl6⟩

end Work.SSGcrux
