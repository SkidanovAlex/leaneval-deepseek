import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.E9c.TransportDefs
import Submission.Work.SSGRoute.E0bDefs
import Submission.Work.SSGRoute.eCoh_map
import Submission.Work.SSGRoute.E7cC.exists_level_unramified_p_dvd_inertiaDeg
import Submission.Work.SSGRoute.E7cC.exists_unramifiedDetector_ExtZ_trivial
import Submission.Work.SSGRoute.local_duality_ext
import Submission.Work.SSGRoute.E7cOmega.ratDivDefs
import Submission.Work.SSGRoute.E7cOmega.ratDivSES
import Submission.Work.SSGRoute.E7cOmega.extClass_comp_injective
import Submission.Work.SSGRoute.E7cOmega.levelPair_ratDivSES_extClass
import Submission.Work.SSGRoute.E7cOmega.extH_unitRep_one_subsingleton
import Submission.Work.E7cOmega.ext_one_unitRep_iso_divRep
import Submission.Work.E7cOmega.levelPair_ratDivSES_extClass_eq_zero_iff
import Submission.Work.E7cOmega.subsingleton_ext_unitRep_ratRep
import Submission.Work.E7cOmega.functional_of_ext_nonzero
import Submission.Work.SSGRoute.e9_caseB_cocycle
import Submission.Work.SSGRoute.SSGStage.exists_regularModule_inert_level
import Submission.Work.SSGRoute.SSGStage.mem_cocycles_coordKer
import Submission.Work.SSGRoute.SSGStage.detectorFixedAux
import Submission.Work.Sha2Lib.unramifiedDetector
import Submission.Work.SSGRoute.Sha2Lib.detectorInterface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

set_option backward.isDefEq.respectTransparency false

namespace Work.SSGRoute.E7cOmega

open SSGRoute.PTExt CategoryTheory

/-- **The Ext-class of a character.**  For a normal subgroup `N ⊴ G` with `G ⧸ N` cyclic of order
`p`, there is a class in `H¹(G, 𝔽_p)` (with trivial coefficients) whose restriction to a subgroup
`D` vanishes exactly when `D ≤ N`. -/
theorem cyclicQuotientClass (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (hcyc : IsCyclic (G ⧸ N)) (hcard : Nat.card (G ⧸ N) = p) :
    ∃ h : extH (Rep.trivial Coeff G (ZMod p)) 1,
      ∀ D : Subgroup G, extHRestrict D h = 0 ↔ D ≤ N := by
  classical
  haveI : Finite (G ⧸ N) :=
    (Nat.card_pos_iff.mp (by rw [hcard]; exact (Fact.out : p.Prime).pos)).2
  -- the identification of the quotient with `ℤ/p`
  have he : G ⧸ N ≃* Multiplicative (ZMod p) := by
    have h := zmodCyclicMulEquiv hcyc
    rw [hcard] at h
    exact h.symm
  -- the corresponding additive character `G → ℤ/p`
  let χ : Additive G →+ ZMod p :=
    { toFun := fun g => (he (QuotientGroup.mk' N (Additive.toMul g))).toAdd
      map_zero' := by simp
      map_add' := fun a b => by simp [toMul_add] }
  have hχker : ∀ g : G, χ (Additive.ofMul g) = 0 ↔ g ∈ N := by
    intro g
    rw [show χ (Additive.ofMul g) = (he (g : G ⧸ N)).toAdd from rfl, toAdd_eq_zero]
    refine ⟨fun h1 => (QuotientGroup.eq_one_iff g).mp (he.injective ?_),
      fun h1 => ?_⟩
    · rw [h1, map_one]
    · rw [(QuotientGroup.eq_one_iff g).mpr h1, map_one]
  -- the cocycle and its class
  let z : groupCohomology.cocycles₁ (Rep.trivial Coeff G (ZMod p)) :=
    ⟨χ ∘ Additive.ofMul,
      groupCohomology.mem_cocycles₁_of_addMonoidHom (A := Rep.trivial Coeff G (ZMod p)) χ⟩
  refine ⟨eCoh 1 G (Rep.trivial Coeff G (ZMod p)) (groupCohomology.H1π _ z), ?_⟩
  intro D
  -- the restriction is computed by the restricted cocycle
  have htriv : SSGRoute.PTExt.trivResInv D.subtype (ZMod p)
      = 𝟙 (Rep.res D.subtype (Rep.trivial Coeff G (ZMod p))) := by
    apply Rep.hom_ext
    ext x
    rfl
  have hH1 : groupCohomology.map D.subtype (SSGRoute.PTExt.trivResInv D.subtype (ZMod p)) 1
        (groupCohomology.H1π _ z)
      = groupCohomology.H1π _ (groupCohomology.mapCocycles₁ D.subtype
          (SSGRoute.PTExt.trivResInv D.subtype (ZMod p)) z) :=
    groupCohomology.H1π_comp_map_apply D.subtype (SSGRoute.PTExt.trivResInv D.subtype (ZMod p)) z
  have hrestrict : extHRestrict D (eCoh 1 G (Rep.trivial Coeff G (ZMod p))
        (groupCohomology.H1π _ z))
      = eCoh 1 D (Rep.trivial Coeff D (ZMod p))
          (groupCohomology.H1π _ (groupCohomology.mapCocycles₁ D.subtype
            (SSGRoute.PTExt.trivResInv D.subtype (ZMod p)) z)) := by
    have h1 : extHRestrict D (eCoh 1 G (Rep.trivial Coeff G (ZMod p))
          (groupCohomology.H1π _ z))
        = extHMap D.subtype (SSGRoute.PTExt.trivResInv D.subtype (ZMod p))
            (eCoh 1 G (Rep.trivial Coeff G (ZMod p)) (groupCohomology.H1π _ z)) := by
      rw [extHRestrict]
      exact congrArg (fun φ => extHMap D.subtype φ
        (eCoh 1 G (Rep.trivial Coeff G (ZMod p)) (groupCohomology.H1π _ z))) htriv
    rw [h1, ← eCoh_map 1 G D D.subtype (Rep.trivial Coeff G (ZMod p))
      (Rep.trivial Coeff D (ZMod p)) (SSGRoute.PTExt.trivResInv D.subtype (ZMod p))
      (groupCohomology.H1π _ z), hH1]
  rw [hrestrict]
  have hzero : eCoh 1 D (Rep.trivial Coeff D (ZMod p))
      (groupCohomology.H1π _ (groupCohomology.mapCocycles₁ D.subtype
        (SSGRoute.PTExt.trivResInv D.subtype (ZMod p)) z)) = 0
      ↔ groupCohomology.mapCocycles₁ D.subtype
          (SSGRoute.PTExt.trivResInv D.subtype (ZMod p)) z = 0 := by
    constructor
    · intro h0
      have h1 : (groupCohomology.H1π _ (groupCohomology.mapCocycles₁ D.subtype
            (SSGRoute.PTExt.trivResInv D.subtype (ZMod p)) z)) = 0 := by
        apply (eCoh 1 D (Rep.trivial Coeff D (ZMod p))).injective
        simp [h0]
      have hmem := (groupCohomology.H1π_eq_zero_iff _).1 h1
      rw [groupCohomology.coboundaries₁_eq_bot_of_isTrivial, Submodule.mem_bot] at hmem
      exact Submodule.coe_eq_zero.mp hmem
    · intro h0
      rw [h0]
      simp
  refine hzero.trans ?_
  -- the restricted cocycle vanishes exactly on `N`
  have hfun : ∀ d : D, (groupCohomology.mapCocycles₁ D.subtype
        (SSGRoute.PTExt.trivResInv D.subtype (ZMod p)) z : D → ZMod p) d
      = χ (Additive.ofMul ((d : D) : G)) := by
    intro d
    rw [groupCohomology.coe_mapCocycles₁]
    rfl
  constructor
  · intro h0 d hd
    have h1 : (groupCohomology.mapCocycles₁ D.subtype
        (SSGRoute.PTExt.trivResInv D.subtype (ZMod p)) z : D → ZMod p) ⟨d, hd⟩ = 0 := by
      rw [h0]; rfl
    rw [hfun] at h1
    exact (hχker d).mp h1
  · intro hDN
    have h1 : (groupCohomology.mapCocycles₁ D.subtype
        (SSGRoute.PTExt.trivResInv D.subtype (ZMod p)) z : D → ZMod p) = 0 := by
      funext d
      rw [hfun]
      exact (hχker ((d : D) : G)).mpr (hDN d.2)
    exact Subtype.ext h1

/-- **The target follows from the `ℚ/ℤ`-coefficient detector.**

If for every nonzero `D_w`-equivariant functional `μ : res M ⟶ ℚ/ℤ` there are a level `L ⊇ K`, a
place `q' ∣ q` with `e(q'|q)` prime to `p`, and an unramified class `h ∈ H¹(Gal(L/k), res M)` whose
restriction to `D_{q'}` pairs nontrivially with `μ`, then the detecting class of the target exists
for `φ = δ(μ)`. -/
theorem exists_level_unramified_detecting_class_of_functional
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (hdet : ∀ μ : Rep.res (decompK (k := k) (K := K) w).subtype M ⟶
        Work.SSGRoute.E7cOmega.divRep (decompK (k := k) (K := K) w), μ ≠ 0 →
      ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
        (_ : IsGalois k ↥L)
        (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
        (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
        (h : extH (Rep.res (galRes k K ↥L) M) 1),
        IsUnramifiedClassAt q' h ∧
        Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p ∧
        (extHRestrict (decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h).comp
          (Abelian.Ext.mk₀ (Rep.resMap
            (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq') μ))
          (add_zero 1) ≠ 0)
    (μ : Rep.res (decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (decompK (k := k) (K := K) w)) (hμ : μ ≠ 0) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
      (h : extH (Rep.res (galRes k K ↥L) M) 1),
      IsUnramifiedClassAt q' h ∧
      Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p ∧
      levelPair (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
        (trivResInv (Work.SSGRoute.decompKRestrict k K ↥L w
          (NK.GlobalCFT.Place.ofFinite q') hq') Coeff)
        ((Abelian.Ext.mk₀ μ).comp
          (ShortComplex.ShortExact.extClass
            (Work.SSGRoute.E7cOmega.ratDivSES_shortExact
              (G := decompK (k := k) (K := K) w))) (zero_add 1))
        (extHRestrict (decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h) ≠ 0 := by
  obtain ⟨L, hLnf, hLfd, hLgal, q', hq', h, hunr, hcop, hval⟩ := hdet μ hμ
  refine ⟨L, hLnf, hLfd, hLgal, q', hq', h, hunr, hcop, ?_⟩
  haveI : Fintype (decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) :=
    Fintype.ofFinite _
  refine fun hzero => hval ?_
  refine (Work.E7cOmega.levelPair_ratDivSES_extClass_eq_zero_iff
    (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq') μ
    (extHRestrict (decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h)
    (Work.E7cOmega.subsingleton_ext_unitRep_ratRep
      (decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')))).mp hzero

/-- **The target follows from the `ℚ/ℤ`-coefficient detector, in `φ`-form.**

Combines `Work.E7cOmega.functional_of_ext_nonzero` (Tate duality produces a nonzero functional `μ`
with `φ = δμ`) with `exists_level_unramified_detecting_class_of_functional`. -/
theorem exists_level_unramified_detecting_class_of_detector
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (hdet : ∀ μ : Rep.res (decompK (k := k) (K := K) w).subtype M ⟶
        Work.SSGRoute.E7cOmega.divRep (decompK (k := k) (K := K) w), μ ≠ 0 →
      ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
        (_ : IsGalois k ↥L)
        (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
        (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
        (h : extH (Rep.res (galRes k K ↥L) M) 1),
        IsUnramifiedClassAt q' h ∧
        Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p ∧
        (extHRestrict (decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h).comp
          (Abelian.Ext.mk₀ (Rep.resMap
            (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq') μ))
          (add_zero 1) ≠ 0)
    (φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1)
    (hφ : φ ≠ 0) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
      (h : extH (Rep.res (galRes k K ↥L) M) 1),
      IsUnramifiedClassAt q' h ∧
      Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p ∧
      levelPair (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
        (trivResInv (Work.SSGRoute.decompKRestrict k K ↥L w
          (NK.GlobalCFT.Place.ofFinite q') hq') Coeff)
        φ
        (extHRestrict (decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h) ≠ 0 := by
  obtain ⟨μ, hμne, hφμ⟩ := Work.E7cOmega.functional_of_ext_nonzero p k K M hM w φ hφ
  obtain ⟨L, hLnf, hLfd, hLgal, q', hq', h, hunr, hcop, hkey⟩ :=
    exists_level_unramified_detecting_class_of_functional p k K Ω M hM w hdet μ hμne
  exact ⟨L, hLnf, hLfd, hLgal, q', hq', h, hunr, hcop, by rw [hφμ]; exact hkey⟩


/-- **The sibling spelling of the node.**  `Work.SSGRoute.Sha2Lib.DetectsAt` is the conclusion of
this file's node verbatim, except that its coprimality clause is stated with Mathlib's older
`Ideal.ramificationIdx'` instead of `Ideal.ramificationIdx`.  The two agree by
`Ideal.ramificationIdx'_eq_ramificationIdx`, so the node follows from the sibling lane's
`IsUnramifiedDetector` node (`Work.Sha2Lib.unramifiedDetector`) — stated here with that node as a
hypothesis, so that this lemma is `sorry`-free and usable no matter when the sibling node lands. -/
theorem exists_level_unramified_detecting_class_of_detectorInterface
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (hdet : Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq M)
    (φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1)
    (hφ : φ ≠ 0) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
      (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M) 1),
      SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
      Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p ∧
      SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k K ↥L w
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L w
          (NK.GlobalCFT.Place.ofFinite q') hq') SSGRoute.PTExt.Coeff)
        φ
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
          (NK.GlobalCFT.Place.ofFinite q')) h) ≠ 0 := by
  obtain ⟨L, hLnf, hLfd, hLgal, q', hq', h, hunr, hcop, hpair⟩ := hdet φ hφ
  refine ⟨L, hLnf, hLfd, hLgal, q', hq', h, hunr, ?_, hpair⟩
  haveI : NumberField ↥L := hLnf
  haveI : FiniteDimensional k ↥L := hLfd
  haveI : IsGalois k ↥L := hLgal
  -- the place-level `LiesOver` gives the ideal-level one (`liesOver_iff`), the finite case being
  -- the only one possible since `q'` is finite
  have hlies : (q'.asIdeal).LiesOver q.asIdeal := by
    have h1 : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
        (NK.GlobalCFT.Place.ofFinite q) := by
      rw [← hwq]
      exact hq'
    rcases (NK.GlobalCFT.Place.liesOver_iff _ _).1 h1 with
      ⟨w', v', hw', hv', -⟩ | ⟨q₁, Q₁, hq1, hQ1, hl⟩
    · exact absurd hw'.symm (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w' q')
    · obtain rfl : q₁ = q' := (NK.GlobalCFT.Place.ofFinite_inj.mp hq1).symm
      obtain rfl : Q₁ = q := (NK.GlobalCFT.Place.ofFinite_inj.mp hQ1).symm
      exact hl
  haveI : (q'.asIdeal).LiesOver q.asIdeal := hlies
  have hram : q.asIdeal.ramificationIdx' q'.asIdeal
      = (q'.asIdeal).ramificationIdx (NumberField.RingOfIntegers K) :=
    Ideal.ramificationIdx'_eq_ramificationIdx q.asIdeal q'.asIdeal q.ne_bot
  rw [← hram]
  exact hcop

/-- **The cohomological core of the detector**: a `Gal(K/k)`-equivariant functional on the kernel of
`galRes k K L`, vanishing on the inertia at `q'` and taking a `μ`-non-zero value at the
`N`-coordinate of some element of the decomposition group, produces a class in
`H¹(Gal(L/k), res M)` which is unramified at `q'` and whose level pairing with `μ` is non-zero.

This is the statement that the *arithmetic* input
(`Work.SSGRoute.E7cOmega.exists_level_detecting_functional`) is exactly what the node needs: the
class is the `eCoh`-class of the cocycle `γ ↦ φ (coordKer γ)`
(`Work.SSGRoute.SSGStage.mem_cocycles_coordKer`), unramifiedness is condition `(2a)` transported
through `Work.SSGRoute.e9_caseB_cocycle`, and non-vanishing of the `μ`-pushforward is condition
`(2b)` transported through
`Work.SSGRoute.SSGStage.extHRestrict_comp_mk0_eq_eCoh_map` +
`Work.SSGRoute.SSGStage.eCoh_map_ne_zero`. -/
theorem exists_detecting_class_of_coord_functional
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (w : NK.GlobalCFT.Place K)
    (L : IntermediateField K Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (s : (K ≃ₐ[k] K) →* (↥L ≃ₐ[k] ↥L))
    (hs : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.galRes k K ↥L (s σ) = σ)
    (φ : Additive ((SSGRoute.PTExt.galRes k K ↥L).ker) →+ M.V)
    (hφ : ∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
      φ (Additive.ofMul ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
          Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩)
        = M.ρ (SSGRoute.PTExt.galRes k K ↥L σ) (φ (Additive.ofMul g)))
    (h2a : ∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
      φ (Additive.ofMul (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ)) = 0)
    (h2b : ∃ d : ↥L ≃ₐ[k] ↥L, d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q') ∧
      μ.hom (φ (Additive.ofMul (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d))) ≠ 0) :
    ∃ h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M) 1,
      SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
      (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
          (NK.GlobalCFT.Place.ofFinite q')) h).comp
        (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap
          (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq') μ))
        (add_zero 1) ≠ 0 := by
  classical
  let A : Rep.{0} SSGRoute.PTExt.Coeff (↥L ≃ₐ[k] ↥L) :=
    Rep.res (SSGRoute.PTExt.galRes k K ↥L) M
  have hφ' : ∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
      φ (Additive.ofMul ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
          Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩)
        = A.ρ σ (φ (Additive.ofMul g)) := by
    intro σ g
    rw [hφ σ g]
    rfl
  let z : ↥(groupCohomology.cocycles₁ A) :=
    ⟨fun γ => φ (Additive.ofMul (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ)),
      Work.SSGRoute.SSGStage.mem_cocycles_coordKer p k K Ω L M s hs φ hφ'⟩
  let h : SSGRoute.PTExt.extH A 1 :=
    SSGRoute.PTExt.eCoh 1 (↥L ≃ₐ[k] ↥L) A ((groupCohomology.H1π A).hom z)
  have hcoe : h = SSGRoute.PTExt.eCoh 1 (↥L ≃ₐ[k] ↥L) A ((groupCohomology.H1π A).hom z) := rfl
  refine ⟨h, ?_, ?_⟩
  · intro D hD
    rw [Work.SSGRoute.e9_caseB_cocycle A D z]
    refine ⟨0, fun d hd => ?_⟩
    have hR : A.ρ d (0 : ↥A) - (0 : ↥A) = (0 : ↥A) := by rw [map_zero, sub_self]
    rw [hR]
    exact h2a d (hD d hd)
  · obtain ⟨d, hdD, hdne⟩ := h2b
    intro hzero
    let D : Subgroup (↥L ≃ₐ[k] ↥L) :=
      SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')
    let B : Rep.{0} SSGRoute.PTExt.Coeff ↥D :=
      Rep.res (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
        (Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    let ν : Rep.res D.subtype A ⟶ B :=
      Rep.resMap (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq') μ
    haveI hB : B.IsTrivial :=
      Work.SSGRoute.SSGStage.isTrivial_res
        (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
        (Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    have hkey := Work.SSGRoute.SSGStage.extHRestrict_comp_mk0_eq_eCoh_map D A B ν h
    have hecoh : (SSGRoute.PTExt.eCoh 1 (↥L ≃ₐ[k] ↥L) A).symm h
        = (groupCohomology.H1π A).hom z := by
      rw [hcoe]
      exact Equiv.symm_apply_apply _ _
    rw [hecoh] at hkey
    have hw : ∃ h₀ : ↥D, ν ((z : (↥L ≃ₐ[k] ↥L) → A.V) (D.subtype h₀)) ≠ 0 := by
      refine ⟨⟨d, hdD⟩, ?_⟩
      have hν : ν ((z : (↥L ≃ₐ[k] ↥L) → A.V) (D.subtype ⟨d, hdD⟩))
          = μ.hom (φ (Additive.ofMul (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d))) := rfl
      rw [hν]
      exact hdne
    refine (Work.SSGRoute.SSGStage.eCoh_map_ne_zero D.subtype A B ν z hw) ?_
    rw [← hkey]
    exact hzero

/-- **The inner-action obstruction.**  (Session 7.)

Let `L ⊇ K` be a finite Galois level over `k`, `N = ker (galRes k K L)`, `G₀ = Gal(K/k)`, and
`φ : N →+ M.V` a `G₀`-equivariant additive map (the equivariance being that of
`SSGRoute.SSGStage.mem_cocycles_coordKer`).  If the conjugation action of `Gal(L/k)` on `N` is
**inner** — i.e. for every `σ : ↥L ≃ₐ[k] ↥L` there is `n₀ ∈ N` with
`σ * g * σ⁻¹ = n₀ * g * n₀⁻¹` for all `g ∈ N` — then `φ` takes values in the `G₀`-invariants of `M`.

*Proof.*  `φ (σ g σ⁻¹) = φ (n₀ g n₀⁻¹) = φ n₀ + φ g - φ n₀ = φ g` by additivity, while
`φ (σ g σ⁻¹) = M.ρ (galRes σ) (φ g)` by equivariance.

**Consequence (why this matters for node `C6`).**  The detecting class of the node is built from the
cocycle `γ ↦ φ (coordKer γ)`: hence its restriction to `D_{q'}` takes values of the form
`μ (φ (coordKer d))` with `φ (coordKer d) ∈ M^{G₀} ⊆ M^{D_w}`.  So at a level whose action is inner,
the detector can **only** detect a functional `μ` with `μ|_{M^{D_w}} ≠ 0` — the case already covered
by `Work.SSGRoute.SSGStage.detector_of_fixedPart`.  In particular the level shape
`L = K·F` with `K ∩ F = k` (`Gal(L/k) = Gal(K/k) × Gal(F/k)`, i.e. a "linearly disjoint
compositum", including the `F = k(ζ_ℓ, ζ_{ℓ'}, β^{1/ℓ})` of
`E7cC/NOTE_C6_session18_tame_detector.md` §3quinquies), and more generally every level with abelian
`Gal(L/k)`, has an inner action — indeed conjugation by `s σ = (σ, ψ σ)` is conjugation by
`(1, ψ σ) ∈ N` — so such levels **cannot** close the remaining case `μ|_{M^{D_w}} = 0`.  A detecting
level must therefore have a *non-inner* `Gal(K/k)`-action on `ker (galRes k K L)`. -/
theorem coordKer_value_mem_invariants (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (L : IntermediateField K Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (s : (K ≃ₐ[k] K) →* (↥L ≃ₐ[k] ↥L))
    (hs : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.galRes k K ↥L (s σ) = σ)
    (φ : Additive ((SSGRoute.PTExt.galRes k K ↥L).ker) →+ M.V)
    (hφ : ∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
      φ (Additive.ofMul ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
          SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩)
        = M.ρ (SSGRoute.PTExt.galRes k K ↥L σ) (φ (Additive.ofMul g)))
    (hinner : ∀ σ : ↥L ≃ₐ[k] ↥L, ∃ n₀ : (SSGRoute.PTExt.galRes k K ↥L).ker,
      ∀ g : (SSGRoute.PTExt.galRes k K ↥L).ker,
        (⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
            SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩ :
          (SSGRoute.PTExt.galRes k K ↥L).ker) = n₀ * g * n₀⁻¹) :
    ∀ g : (SSGRoute.PTExt.galRes k K ↥L).ker, ∀ σ : K ≃ₐ[k] K,
      M.ρ σ (φ (Additive.ofMul g)) = φ (Additive.ofMul g) := by
  intro g σ
  have h1 := hφ (s σ) g
  rw [hs σ] at h1
  have h2 : φ (Additive.ofMul (⟨s σ * (g : ↥L ≃ₐ[k] ↥L) * (s σ)⁻¹,
      SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L (s σ) g⟩ :
        (SSGRoute.PTExt.galRes k K ↥L).ker)) = φ (Additive.ofMul g) := by
    obtain ⟨n₀, hn₀⟩ := hinner (s σ)
    rw [hn₀ g]
    have h3 : (Additive.ofMul (n₀ * g * n₀⁻¹) : Additive (SSGRoute.PTExt.galRes k K ↥L).ker)
        = Additive.ofMul n₀ + Additive.ofMul g - Additive.ofMul n₀ := by
      simp [sub_eq_add_neg, add_assoc]
    rw [h3, map_sub, map_add]
    abel
  rw [h2] at h1
  exact h1.symm

/-- **Node `C6` of the E7cΩ route: the unramified detector, in `ℤ`-coefficient form, in the
`E7cOmega` spelling.**

State of the proof (session 6):

* the cohomological half is *proved* in this file (`exists_detecting_class_of_coord_functional`,
  `exists_level_unramified_detecting_class_of_functional`, `…_of_detector`);
* the arithmetic half (the level and the `φ ∘ coordKer` detecting functional) is **not** formalised
  anywhere: the statement that used to be handed out for it
  (`Work.SSGRoute.E7cOmega.exists_level_detecting_functional` = `SSGStage.detectingFunctional`) was
  declared **FALSE** by a prover (`SSGRoute/PING_C6_input_declared_false.md`), because the detecting
  classes of the true route are the Shapiro/commutator classes over `F = K^{D_w}`
  (`E7cC/NOTE_C6_session17_level_via_weakApproximation.md` §1, §7) and are provably not of the
  coordinate form;
* consequently the node is wired, through the proved bridge
  `exists_level_unramified_detecting_class_of_detectorInterface`, to the **detector itself** —
  `Work.Sha2Lib.unramifiedDetector` / `Work.SSGRoute.Sha2Lib.IsUnramifiedDetector` — which is the
  statement that all lanes agree is *true* (see `E7cC/NOTE_C6_session16_truth_and_pPart.md` §1) and
  which is *equivalent* to this node up to the `ramificationIdx'` spelling.  So this node closes as
  soon as the detector is proved in that spelling, whoever proves it; the fleet lanes
  (`Sha2Lib`, `SSGStage`, `E7cC`, `HSRow`) are building exactly that (`indDatum*`,
  `exists_invariant_datum_functional`, `exists_induced_level_augDetecting`, …);
* if instead the *level-shaped* route is ever resumed successfully, the one-line alternative proof
  body is the one recorded in `E7cOmega/NOTE_C6_session6.md` §2/§3 (it uses
  `exists_level_detecting_functional` + `exists_detecting_class_of_coord_functional`). -/
theorem exists_level_unramified_detecting_class (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1)
    (hφ : φ ≠ 0) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
      (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M) 1),
      SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
      Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p ∧
      SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq') SSGRoute.PTExt.Coeff)
        φ
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h) ≠ 0 := by
  exact exists_level_unramified_detecting_class_of_detectorInterface p k K Ω M hM w q hwq hpq hI
    (Work.Sha2Lib.unramifiedDetector p k K Ω w q hwq hpq M hM hI) φ hφ

end Work.SSGRoute.E7cOmega
