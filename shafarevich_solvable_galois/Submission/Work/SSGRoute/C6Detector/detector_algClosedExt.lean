import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.Sha2Lib.detectorInterface
import Submission.Work.SSGRoute.Sha2Lib.galRes_autCongr_symm
import Submission.Work.SSGRoute.Sha2Lib.isInertiaAt_map_algEquiv
import Submission.Work.SSGRoute.extHRestrict_inflHIn_eq_zero_of_forall
import Submission.Work.SSGRoute.extRes_injective_of_mulEquiv
import Submission.Work.SSGRoute.levelPair_baseChange_key

/-!
# Independence of the unramified detector of the ambient algebraically closed field

If the unramified detector `IsUnramifiedDetector p k K Ω₀ w q hwq M` holds in one algebraically
closed extension `Ω₀ ⊇ K` (over `k`), then it holds in any other algebraically closed extension
`Ω ⊇ K` that receives `Ω₀` through a `k`-algebra embedding which fixes `K`.

The only place the ambient field enters the conclusion `DetectsAt` is the binding
`∃ L : IntermediateField K Ω` of the level, so it suffices to realise a level `L₀ ⊆ Ω₀` produced by
the detector inside `Ω` as the image `L₀.map φ`, and to transport the finite Galois-theoretic data
(the place, the class in `H¹`, the inertia condition and the level pairing) along the
`K`-algebra isomorphism `↥L₀ ≃ₐ[K] ↥L`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.SSGRoute.C6Detector

open CategoryTheory SSGRoute.PTExt
open scoped NumberField

/-! ## Abstract `Ext`-calculus -/

/-- **The level pairing is unchanged by moving a transport from the coefficient morphism into the
group homomorphism.** -/
theorem levelPair_congr_hom' {G H : Type} [Group G] [Group H] (f f' : H →* G) (hff : f = f')
    (A : Rep.{0} Coeff G) (x : Abelian.Ext.{0} A (unitRep G) 1) (h' : extH (Rep.res f' A) 1) :
    levelPair f (trivResInv f Coeff) x
      (h'.comp (Abelian.Ext.mk₀ (eqToHom (congrArg (fun t => Rep.res t A) hff.symm)))
        (add_zero 1))
    = levelPair f' (trivResInv f' Coeff) x h' := by
  cases hff
  rw [show congrArg (fun t => Rep.res t A) (rfl : f = f).symm = rfl from Subsingleton.elim _ _,
    eqToHom_refl]
  simp only [levelPair, extRes]
  rw [Abelian.Ext.comp_mk₀_id]

/-- The change-of-group map of a class is its change of group with the identity coefficient
morphism, post-composed with the coefficient morphism. -/
theorem extHMap_eq_comp_mk₀ {G H : Type} [Group G] [Group H] (f : H →* G) {A : Rep.{0} Coeff G}
    {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) {n : ℕ} (y : extH A n) :
    extHMap f ι y = (extHMap f (𝟙 (Rep.res f A)) y).comp
      (Abelian.Ext.mk₀ ι) (add_zero n) := by
  rw [Work.SSGRoute.Y3Key.extHMap_eq_comp f ι y,
    Work.SSGRoute.Y3Key.extHMap_eq_comp f (𝟙 (Rep.res f A)) y]
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero]
  rw [Abelian.Ext.mk₀_comp_mk₀, Category.id_comp]

/-- **The level pairing is transported by a group isomorphism.**  Pushing the value of the level
pairing at a level `ρ₀` along the isomorphism `Ψ` (i.e. restricting to the group `H`) is the level
pairing at the restricted level `ρ₀ ∘ Ψ`, paired with the restriction of the class. -/
theorem levelPair_transport_eq' {G H H₀ : Type} [Group G] [Group H] [Group H₀]
    (Ψ : H ≃* H₀) (ρ₀ : H₀ →* G) (X : Rep.{0} Coeff G)
    (x : Abelian.Ext X (unitRep G) 1) (h₀ : extH (Rep.res ρ₀ X) 1) :
    levelPair (ρ₀.comp Ψ.toMonoidHom) (trivResInv (ρ₀.comp Ψ.toMonoidHom) Coeff) x
        ((extHMap Ψ.toMonoidHom (𝟙 (Rep.res Ψ.toMonoidHom (Rep.res ρ₀ X))) h₀ :
          extH (Rep.res (ρ₀.comp Ψ.toMonoidHom) X) 1))
      = extHMap Ψ.toMonoidHom (trivResInv Ψ.toMonoidHom Coeff)
          (levelPair ρ₀ (trivResInv ρ₀ Coeff) x h₀) := by
  exact (Work.SSGRoute.Y3Key.levelPair_restrict' (f := ρ₀) (g := Ψ.toMonoidHom)
    (ι := trivResInv ρ₀ Coeff) (ιg := trivResInv Ψ.toMonoidHom Coeff)
    (ι' := trivResInv (ρ₀.comp Ψ.toMonoidHom) Coeff) (x := x) (h := h₀) rfl).symm

/-- **Nonvanishing of the level pairing is transported by a group isomorphism.** -/
theorem levelPair_transport_ne_zero' {G H H₀ : Type} [Group G] [Group H] [Group H₀]
    (Ψ : H ≃* H₀) (ρ₀ : H₀ →* G) (X : Rep.{0} Coeff G)
    (x : Abelian.Ext X (unitRep G) 1) (h₀ : extH (Rep.res ρ₀ X) 1)
    (h : levelPair ρ₀ (trivResInv ρ₀ Coeff) x h₀ ≠ 0) :
    levelPair (ρ₀.comp Ψ.toMonoidHom) (trivResInv (ρ₀.comp Ψ.toMonoidHom) Coeff) x
        ((extHMap Ψ.toMonoidHom (𝟙 (Rep.res Ψ.toMonoidHom (Rep.res ρ₀ X))) h₀ :
          extH (Rep.res (ρ₀.comp Ψ.toMonoidHom) X) 1)) ≠ 0 := by
  rw [levelPair_transport_eq' Ψ ρ₀ X x h₀]
  have hEq : extHMap Ψ.toMonoidHom (trivResInv Ψ.toMonoidHom Coeff)
      (levelPair ρ₀ (trivResInv ρ₀ Coeff) x h₀)
      = extRes Ψ.toMonoidHom (levelPair ρ₀ (trivResInv ρ₀ Coeff) x h₀) := by
    rw [Work.SSGRoute.Y3Key.extHMap_eq_comp]
    rw [show (trivResInv Ψ.toMonoidHom Coeff :
        Rep.res Ψ.toMonoidHom (unitRep H₀) ⟶ unitRep H)
        = 𝟙 (Rep.res Ψ.toMonoidHom (unitRep H₀)) from rfl]
    rw [Abelian.Ext.comp_mk₀_id]
  rw [hEq]
  intro h0
  exact h (Work.SSGRoute.extRes_injective_of_mulEquiv Ψ (unitRep H₀) (unitRep H₀) 2
    (by show extRes Ψ.toMonoidHom (levelPair ρ₀ (trivResInv ρ₀ Coeff) x h₀)
              = extRes Ψ.toMonoidHom 0
        rw [h0, Work.SSGRoute.E6Util.extRes_zero]))

/-! ## Transport of decomposition groups along a `K`-algebra isomorphism -/

/-- Composition of `Ideal.map` along a ring equivalence is injective. -/
theorem ideal_map_injective_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (E : R ≃+* S) : Function.Injective (Ideal.map (E : R →+* S)) := by
  intro I J h
  have h1 := congrArg (Ideal.map (E.symm : S →+* R)) h
  rw [Ideal.map_map, Ideal.map_map] at h1
  have hs : (E.symm : S →+* R).comp (E : R →+* S) = RingHom.id R := by
    ext x
    exact E.symm_apply_apply x
  rw [hs, Ideal.map_id, Ideal.map_id] at h1
  exact h1

/-- **Decomposition groups transport along a `K`-algebra isomorphism of number fields.**  For
`e : A ≃ₐ[K] B` and `q' = e_*(q)` the conjugation `(autCongr (e|_k)).symm` carries the decomposition
group of `q'` onto the decomposition group of `q`. -/
theorem decompK_map_autCongr_symm' {k K A B : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Field A] [NumberField A] [Field B] [NumberField B]
    [Algebra k K] [Algebra K A] [Algebra K B] [Algebra k A] [Algebra k B]
    [IsScalarTower k K A] [IsScalarTower k K B]
    (e : A ≃ₐ[K] B) (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers A))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers B))
    (hq' : q'.asIdeal = q.asIdeal.map
      (NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv) :
    (SSGRoute.PTExt.decompK (k := k) (K := B)
        (NK.GlobalCFT.Place.ofFinite q')).map
        (AlgEquiv.autCongr (e.restrictScalars k)).symm.toMonoidHom
      = SSGRoute.PTExt.decompK (k := k) (K := A)
        (NK.GlobalCFT.Place.ofFinite q) := by
  -- the elementwise criterion: conjugating by `e` exchanges the two decomposition groups
  have hcrit : ∀ u : A ≃ₐ[k] A,
      (AlgEquiv.autCongr (e.restrictScalars k)) u ∈
          SSGRoute.PTExt.decompK (k := k) (K := B) (NK.GlobalCFT.Place.ofFinite q')
        ↔ u ∈ SSGRoute.PTExt.decompK (k := k) (K := A) (NK.GlobalCFT.Place.ofFinite q) := by
    intro u
    have hmemA : ∀ v : A ≃ₐ[k] A, v ∈ SSGRoute.PTExt.decompK (k := k) (K := A)
        (NK.GlobalCFT.Place.ofFinite q)
        ↔ Ideal.map (NK.GlobalCFT.Place.ringOfIntegersEquiv v) q.asIdeal = q.asIdeal := by
      intro v
      rw [SSGRoute.PTExt.decompK, MulAction.mem_stabilizer_iff,
        NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj,
        IsDedekindDomain.HeightOneSpectrum.ext_iff,
        NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
    have hmemB : ∀ v : B ≃ₐ[k] B, v ∈ SSGRoute.PTExt.decompK (k := k) (K := B)
        (NK.GlobalCFT.Place.ofFinite q')
        ↔ Ideal.map (NK.GlobalCFT.Place.ringOfIntegersEquiv v) q'.asIdeal = q'.asIdeal := by
      intro v
      rw [SSGRoute.PTExt.decompK, MulAction.mem_stabilizer_iff,
        NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj,
        IsDedekindDomain.HeightOneSpectrum.ext_iff,
        NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
    rw [hmemA u, hmemB ((AlgEquiv.autCongr (e.restrictScalars k)) u)]
    -- the ring-of-integers homs, named
    let ER : 𝓞 A ≃+* 𝓞 B := (NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv
    let E : 𝓞 A →+* 𝓞 B := ER
    let S : 𝓞 B →+* 𝓞 B :=
      NK.GlobalCFT.Place.ringOfIntegersEquiv ((AlgEquiv.autCongr (e.restrictScalars k)) u)
    let U : 𝓞 A →+* 𝓞 A := NK.GlobalCFT.Place.ringOfIntegersEquiv u
    have hq'E : q'.asIdeal = Ideal.map E q.asIdeal := hq'
    -- the key identity of ring homomorphisms
    have hkey : S.comp E = E.comp U := by
      have hcoe : ∀ y : 𝓞 A,
          (((NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv) y : B) = e (y : A) :=
        fun y => rfl
      ext x
      simp only [S, E, ER, U, RingHom.comp_apply, RingEquiv.coe_toRingHom,
        NK.GlobalCFT.Place.ringOfIntegersEquiv_apply, AlgEquiv.autCongr_apply,
        AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply, AlgEquiv.symm_restrictScalars]
      rw [hcoe x, AlgEquiv.symm_apply_apply,
        hcoe ((NK.GlobalCFT.Place.ringOfIntegersEquiv u) x),
        NK.GlobalCFT.Place.ringOfIntegersEquiv_apply]
    have hiff : (Ideal.map S (Ideal.map E q.asIdeal) = Ideal.map E q.asIdeal)
        ↔ (Ideal.map U q.asIdeal = q.asIdeal) := by
      constructor
      · intro h
        have h1 : Ideal.map S (Ideal.map E q.asIdeal)
            = Ideal.map E (Ideal.map U q.asIdeal) := by
          calc Ideal.map S (Ideal.map E q.asIdeal)
              = Ideal.map (S.comp E) q.asIdeal := Ideal.map_map E S
            _ = Ideal.map (E.comp U) q.asIdeal := by rw [hkey]
            _ = Ideal.map E (Ideal.map U q.asIdeal) := (Ideal.map_map U E).symm
        exact (ideal_map_injective_of_ringEquiv ER).eq_iff.mp (h1.symm.trans h)
      · intro h
        calc Ideal.map S (Ideal.map E q.asIdeal)
            = Ideal.map (S.comp E) q.asIdeal := Ideal.map_map E S
          _ = Ideal.map (E.comp U) q.asIdeal := by rw [hkey]
          _ = Ideal.map E (Ideal.map U q.asIdeal) := (Ideal.map_map U E).symm
          _ = Ideal.map E q.asIdeal := by rw [h]
    rw [hq'E]
    exact hiff
  refine le_antisymm ?_ ?_
  · intro τ hτ
    rw [Subgroup.mem_map] at hτ
    obtain ⟨σ, hσ, rfl⟩ := hτ
    have happ : (AlgEquiv.autCongr (e.restrictScalars k))
        ((AlgEquiv.autCongr (e.restrictScalars k)).symm.toMonoidHom σ) = σ := by
      show (AlgEquiv.autCongr (e.restrictScalars k))
          ((AlgEquiv.autCongr (e.restrictScalars k)).symm σ) = σ
      exact MulEquiv.apply_symm_apply _ σ
    exact (hcrit _).mp (happ.symm ▸ hσ)
  · intro τ hτ
    exact Subgroup.mem_map.mpr ⟨(AlgEquiv.autCongr (e.restrictScalars k)) τ,
      (hcrit τ).mpr hτ, by
        exact MulEquiv.symm_apply_apply _ τ⟩

/-! ## The transport of the detector -/

theorem detector_algClosedExt (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K]
    (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra k Ω₀] [Algebra k Ω] [Algebra K Ω₀] [Algebra K Ω]
    [IsScalarTower k K Ω₀] [IsScalarTower k K Ω] [IsAlgClosed Ω₀] [IsAlgClosed Ω]
    (φ : Ω₀ →ₐ[k] Ω) (hφ : Function.Injective φ)
    (hφK : ∀ x : K, φ (algebraMap K Ω₀ x) = algebraMap K Ω x)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω₀ w q hwq M →
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq M := by
  intro hdet
  unfold Work.SSGRoute.Sha2Lib.IsUnramifiedDetector at hdet ⊢
  unfold Work.SSGRoute.Sha2Lib.DetectsAt at hdet ⊢
  intro φe hφe
  obtain ⟨L₀, hL₀nf, hL₀fd, hL₀gal, q₀, hq₀, h₀, hunr₀, hcop₀, hpair₀⟩ := hdet φe hφe
  haveI : NumberField ↥L₀ := hL₀nf
  haveI : FiniteDimensional k ↥L₀ := hL₀fd
  haveI : IsGalois k ↥L₀ := hL₀gal
  -- ## The transported level, inside `Ω`
  let φK : Ω₀ →ₐ[K] Ω := { φ.toRingHom with commutes' := hφK }
  let L : IntermediateField K Ω := L₀.map φK
  let e : ↥L₀ ≃ₐ[K] ↥L := IntermediateField.equivMap L₀ φK
  haveI : FiniteDimensional k ↥L :=
    FiniteDimensional.of_injective (e.restrictScalars k).symm.toLinearEquiv.toLinearMap
      (e.restrictScalars k).symm.injective
  haveI : NumberField ↥L := NumberField.of_module_finite k ↥L
  haveI : IsGalois k ↥L := IsGalois.of_algEquiv (e.restrictScalars k)
  -- ## The conjugation isomorphism `Gal(↥L/k) ≃* Gal(↥L₀/k)`
  let ek : ↥L₀ ≃ₐ[k] ↥L := e.restrictScalars k
  let Φ : (↥L ≃ₐ[k] ↥L) →* (↥L₀ ≃ₐ[k] ↥L₀) := (AlgEquiv.autCongr ek).symm.toMonoidHom
  have hcomp : (galRes k K ↥L₀).comp Φ = galRes k K ↥L := by
    refine MonoidHom.ext (fun σ => ?_)
    exact Work.SSGRoute.Sha2Lib.galRes_autCongr_symm e σ
  let Dw : Subgroup (K ≃ₐ[k] K) := decompK (k := k) (K := K) w
  let X : Rep.{0} Coeff Dw := Rep.res Dw.subtype M
  -- ## The transported class `h`
  let h : extH (Rep.res (galRes k K ↥L) M) 1 :=
    extHMap Φ (eqToHom (congrArg (fun t => Rep.res t M) hcomp)) h₀
  -- ## The transported place `q'`
  have hq₀'' : q₀.asIdeal.LiesOver q.asIdeal := by
    have h' := hq₀
    rw [hwq] at h'
    rw [NK.GlobalCFT.Place.liesOver_iff] at h'
    rcases h' with ⟨w', v', h1, h2, _⟩ | ⟨q₁, Q, h1, h2, h3⟩
    · exact absurd h1 (fun he => NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w' q₀ he.symm)
    · rw [NK.GlobalCFT.Place.ofFinite_inj] at h1 h2
      exact h1.symm ▸ h2.symm ▸ h3
  let eO : 𝓞 ↥L₀ ≃ₐ[𝓞 K] 𝓞 ↥L := NumberField.RingOfIntegers.mapAlgEquiv e
  let q' : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥L) :=
    ⟨q₀.asIdeal.map (eO : 𝓞 ↥L₀ →+* 𝓞 ↥L),
      Ideal.map_isPrime_of_equiv (eO : 𝓞 ↥L₀ ≃+* 𝓞 ↥L),
      fun hbot => q₀.ne_bot
        ((Ideal.map_eq_bot_iff_of_injective (eO : 𝓞 ↥L₀ ≃+* 𝓞 ↥L).injective).mp hbot)⟩
  have hq'_asIdeal : q'.asIdeal
      = q₀.asIdeal.map (NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv := rfl
  have hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w := by
    rw [hwq]
    exact NK.GlobalCFT.Place.liesOver_ofFinite (Ideal.map_equiv_liesOver q₀.asIdeal q.asIdeal eO)
  have hcop : Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p := by
    have h1 : q.asIdeal.ramificationIdx' q'.asIdeal = q.asIdeal.ramificationIdx' q₀.asIdeal := by
      rw [hq'_asIdeal]
      exact Ideal.ramificationIdx'_map_eq (p := q.asIdeal) (P := q₀.asIdeal) (e := eO)
    rw [h1]
    exact hcop₀
  -- ## The decomposition groups and the subgroup isomorphism
  let D : Subgroup (↥L ≃ₐ[k] ↥L) := decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')
  let D₀ : Subgroup (↥L₀ ≃ₐ[k] ↥L₀) := decompK (k := k) (K := ↥L₀) (NK.GlobalCFT.Place.ofFinite q₀)
  have hED : D.map Φ = D₀ := decompK_map_autCongr_symm' e q₀ q' hq'_asIdeal
  let Ψ : D ≃* D₀ := (Subgroup.equivMapOfInjective D Φ (AlgEquiv.autCongr ek).symm.injective).trans
    (MulEquiv.subgroupCongr hED)
  have hf : Φ.comp D.subtype = D₀.subtype.comp Ψ.toMonoidHom := rfl
  -- ## Unramifiedness of `h`
  have hunr : IsUnramifiedClassAt q' h := by
    intro Dsub hD
    let Dsub₀ : Subgroup (↥L₀ ≃ₐ[k] ↥L₀) := Dsub.map Φ
    let ΨD : Dsub ≃* Dsub₀ := Subgroup.equivMapOfInjective Dsub Φ
      (AlgEquiv.autCongr ek).symm.injective
    have hfD : Φ.comp Dsub.subtype = Dsub₀.subtype.comp ΨD.toMonoidHom := rfl
    rw [show h = extHMap Φ (eqToHom (congrArg (fun t => Rep.res t M) hcomp)) h₀ from rfl]
    rw [Work.SSGRoute.extHRestrict_extHMap_gen Φ (eqToHom (congrArg (fun t => Rep.res t M) hcomp))
      Dsub Dsub₀ ΨD hfD h₀]
    have hzero : extHRestrict Dsub₀ h₀ = 0 := by
      refine hunr₀ Dsub₀ (fun τ hτ => ?_)
      rw [Subgroup.mem_map] at hτ
      obtain ⟨σ, hσ, rfl⟩ := hτ
      exact (Work.SSGRoute.Sha2Lib.isInertiaAt_map_algEquiv e q₀ q' hq'_asIdeal σ).mp (hD σ hσ)
    rw [hzero]
    exact Work.SSGRoute.E6Util.extHMap_zero _ _
  -- ## The level pairing
  have hpair : levelPair (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
      (trivResInv (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq') Coeff)
      φe (extHRestrict D h) ≠ 0 := by
    let ρ : D →* Dw := Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq'
    let ρ₀ : D₀ →* Dw := Work.SSGRoute.decompKRestrict k K ↥L₀ w (NK.GlobalCFT.Place.ofFinite q₀) hq₀
    let z : extH (Rep.res ρ₀ X) 1 := extHRestrict D₀ h₀
    let εG : Rep.res Φ (Rep.res (galRes k K ↥L₀) M) ⟶ Rep.res (galRes k K ↥L) M :=
      eqToHom (congrArg (fun t => Rep.res t M) hcomp)
    show levelPair ρ (trivResInv ρ Coeff) φe (extHRestrict D h) ≠ 0
    have hρ : ρ = ρ₀.comp Ψ.toMonoidHom := by
      refine MonoidHom.ext (fun σ => Subtype.ext ?_)
      show ((ρ σ : Dw) : K ≃ₐ[k] K) = ((ρ₀ (Ψ σ) : Dw) : K ≃ₐ[k] K)
      rw [Work.SSGRoute.decompKRestrict_coe, Work.SSGRoute.decompKRestrict_coe]
      show galRes k K ↥L (σ : ↥L ≃ₐ[k] ↥L) = galRes k K ↥L₀ (Ψ σ : ↥L₀ ≃ₐ[k] ↥L₀)
      rw [show ((Ψ σ : D₀) : ↥L₀ ≃ₐ[k] ↥L₀) = Φ (σ : ↥L ≃ₐ[k] ↥L) from rfl]
      exact (Work.SSGRoute.Sha2Lib.galRes_autCongr_symm e (σ : ↥L ≃ₐ[k] ↥L)).symm
    have hstep1 : extHRestrict D h = extHMap (D₀.subtype.comp Ψ.toMonoidHom)
        (Rep.resMap D.subtype εG ≫ 𝟙 (Rep.res D.subtype (Rep.res (galRes k K ↥L) M))) h₀ := by
      rw [show h = extHMap Φ εG h₀ from rfl]
      rw [show extHRestrict D (extHMap Φ εG h₀)
        = extHMap D.subtype (𝟙 (Rep.res D.subtype (Rep.res (galRes k K ↥L) M)))
            (extHMap Φ εG h₀) from rfl]
      exact Work.SSGRoute.extHMap_comp_aux Φ D.subtype εG
        (𝟙 (Rep.res D.subtype (Rep.res (galRes k K ↥L) M)))
        (Rep.resMap D.subtype εG ≫ 𝟙 (Rep.res D.subtype (Rep.res (galRes k K ↥L) M))) rfl h₀
    have hstep4 : extHMap Ψ.toMonoidHom (𝟙 (Rep.res Ψ.toMonoidHom (Rep.res ρ₀ X))) z
        = extHMap (D₀.subtype.comp Ψ.toMonoidHom)
            (𝟙 (Rep.res (D₀.subtype.comp Ψ.toMonoidHom) (Rep.res (galRes k K ↥L₀) M))) h₀ := by
      show extHMap Ψ.toMonoidHom (𝟙 (Rep.res Ψ.toMonoidHom (Rep.res ρ₀ X)))
          (extHMap D₀.subtype (𝟙 (Rep.res D₀.subtype (Rep.res (galRes k K ↥L₀) M))) h₀)
        = extHMap (D₀.subtype.comp Ψ.toMonoidHom)
            (𝟙 (Rep.res (D₀.subtype.comp Ψ.toMonoidHom) (Rep.res (galRes k K ↥L₀) M))) h₀
      exact Work.SSGRoute.extHMap_comp_aux D₀.subtype Ψ.toMonoidHom
        (𝟙 (Rep.res D₀.subtype (Rep.res (galRes k K ↥L₀) M)))
        (𝟙 (Rep.res Ψ.toMonoidHom (Rep.res D₀.subtype (Rep.res (galRes k K ↥L₀) M))))
        (𝟙 (Rep.res (D₀.subtype.comp Ψ.toMonoidHom) (Rep.res (galRes k K ↥L₀) M)))
        (by
          rw [show Rep.resMap Ψ.toMonoidHom (𝟙 (Rep.res D₀.subtype (Rep.res (galRes k K ↥L₀) M)))
              = 𝟙 (Rep.res Ψ.toMonoidHom (Rep.res D₀.subtype (Rep.res (galRes k K ↥L₀) M))) from
              (Rep.resFunctor Ψ.toMonoidHom).map_id _]
          exact Category.id_comp _) h₀
    have hε : Rep.resMap D.subtype εG ≫ 𝟙 (Rep.res D.subtype (Rep.res (galRes k K ↥L) M))
        = eqToHom (congrArg (fun t => Rep.res t X) hρ.symm) := by
      rw [Category.comp_id]
      rw [show εG = eqToHom (congrArg (fun t => Rep.res t M) hcomp) from rfl]
      rw [show Rep.resMap D.subtype (eqToHom (congrArg (fun t => Rep.res t M) hcomp))
          = (Rep.resFunctor D.subtype).map
              (eqToHom (congrArg (fun t => Rep.res t M) hcomp)) from rfl]
      rw [CategoryTheory.eqToHom_map]
    have hclass : extHRestrict D h
        = (extHMap Ψ.toMonoidHom (𝟙 (Rep.res Ψ.toMonoidHom (Rep.res ρ₀ X))) z).comp
            (Abelian.Ext.mk₀ (eqToHom (congrArg (fun t => Rep.res t X) hρ.symm)))
            (add_zero 1) := by
      rw [hstep1]
      rw [extHMap_eq_comp_mk₀ (D₀.subtype.comp Ψ.toMonoidHom)
        (Rep.resMap D.subtype εG ≫ 𝟙 (Rep.res D.subtype (Rep.res (galRes k K ↥L) M))) h₀]
      rw [← hstep4, ← hε]
    have h1 := levelPair_transport_ne_zero' Ψ ρ₀ X φe z hpair₀
    have h2 := levelPair_congr_hom' ρ (ρ₀.comp Ψ.toMonoidHom) hρ X φe
      (extHMap Ψ.toMonoidHom (𝟙 (Rep.res Ψ.toMonoidHom (Rep.res ρ₀ X))) z)
    rw [hclass, h2]
    exact h1
  exact ⟨L, inferInstance, inferInstance, inferInstance, q', hq', h, hunr, hcop, hpair⟩

end Work.SSGRoute.C6Detector
