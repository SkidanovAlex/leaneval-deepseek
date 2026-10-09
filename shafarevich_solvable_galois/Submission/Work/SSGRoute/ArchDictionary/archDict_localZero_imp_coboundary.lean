import Mathlib
import Submission.Work.SSGRoute.ArchDictionary.Defs
import Submission.Work.SSGRoute.ArchDictionary.AcOdd
import Submission.Work.SSGRoute.ArchDictionary.archCruxLinkedGen
import Submission.Work.SSGRoute.ArchDictionary.coeff_two_coboundary_iff
import Submission.Work.SSGRoute.ArchDictionary.placeLocalFieldComplex
import Submission.Work.SSGRoute.ArchDictionary.exists_extension_of_extRes_comp_mk0_eq_zero
import Submission.Work.SSGRoute.ArchDictionary_aux.psiEMap_sub_betaRaw_mem_range
import Submission.Work.SSGRoute.E1aClean.ArchSeam
import Submission.Work.SSGRoute.PT.decompK_linked
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The kernel clause of the archimedean dictionary, in the "localisation zero" direction

This file proves `Work.SSGRoute.ArchDictionary.archDict_localZero_imp_coboundary`: for a global
locally constant `1`-cocycle `b` of `Gal(Ω/k)` with values in `E`, the *vanishing of the
localisation at the archimedean place `w`* of the canonical global Kummer dictionary class of `b`
forces `b|⟨c⟩` to be a coboundary on the involution group `⟨c⟩`.

## Contents

* `IsCocycleOn.mono` — restriction of a cocycle to a subgroup (formal).
* `isCoboundaryOn_of_mem_B1` — the converse of the (proved)
  `resZ1_mem_absB1_of_isCoboundaryOn`: membership of the restricted cocycle in `B¹(⟨c⟩,E)` is the
  same as `IsCoboundaryOn`, with the same witness (formal bookkeeping of the two actions).
* `archDict_resH1_zpowers_eq_zero_imp_coboundary` — the **assembly**: if the `E1c` class
  `e1cMap 𝓔 (globalDictionaryCanon … b)` of the canonical global dictionary class of `b` restricts
  to `0` on `⟨c⟩`, then `b|⟨c⟩` is a coboundary.  This is the last step of the target once the
  comparison square has produced the vanishing of that `E1c` class, and it is the formal inverse of
  the computation used in `ArchDictionary/archDictCoboundaryImpLocalZero`.
* `archDict_localZero_imp_coboundary_odd` — the target for `p ≠ 2`, where it is *free*: every
  `1`-cocycle on the involution group `⟨c⟩` is a coboundary (`AcOdd.isCoboundaryOn_of_odd`), so the
  hypothesis is not even needed.
* the target itself, split by `p = 2`; the `p = 2` case (`…two`) is the arithmetic content and the
  only remaining `sorry` of this file.

## State of the `p = 2` case

The route is fully mapped in `ArchDictionary/NOTE_localZero_imp_coboundary_strategy.md` (updated)
and in `ArchDictionary/NOTE_p2_body_attempt.lean.txt`, which holds a nearly complete draft of the
`p = 2` argument developed against the API (the errors remaining there are mechanical / instance
issues, not mathematical ones).  The ingredients already on disk and used by the draft:

* `ArchDictionary.exists_extension_of_extRes_comp_mk0_eq_zero` (**proved in this session**) — the
  `⟹` direction of the extension criterion at a place `q`, for an *arbitrary* coefficient
  representation (this is the shape the archimedean application needs; the originally requested
  statement had the first variable specialised to `kernel (freeCover N)`, which is the `_syzygy`
  corollary of that file);
* `ArchDictionary_aux.psiEMap_sub_betaRaw_mem_range` (proved) — the decomposition
  `ΨE y = piH (liftOf cf) + piH0 Φ₀`;
* `ArchDictionary.place_localField_equiv_complex_of_decompK_ne_bot` and
  `ArchDictionary.unitsToLocalUnitsHom_eq_embedding` (proved) — the spelling of `K_wˣ` as `ℂˣ`;
* `E1aClean.ArchSeam.{seamLevelConj, localActionC_eq_conj}` (proved) — the local `D_w`-action on
  `ℂˣ` is complex conjugation;
* `ArchDictionary.coeff_two_coboundary_iff` (proved) — the final `p = 2` algebra.
-/

namespace Work.SSGRoute.ArchDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

noncomputable section

/-- A cocycle on a group restricts to a cocycle on a subgroup. -/
theorem IsCocycleOn.mono {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] {act : Γ →* G} {H H' : Subgroup Γ} (h : H ≤ H') {f : Γ → M}
    (hf : SSGRoute.IsCocycleOn act H' f) : SSGRoute.IsCocycleOn act H f :=
  fun g hg h' hh' => hf g (h hg) h' (h hh')

/-- **The converse of `resZ1_mem_absB1_of_isCoboundaryOn`.**  If the restriction of a cocycle `b` to
`H = ⟨c⟩` is a member of `B¹(H,E)` (in the shape consumed by `resH1`), then `b` is a coboundary on
`H` in the target's notation `IsCoboundaryOn`; the witness is the same `m`. -/
theorem isCoboundaryOn_of_mem_B1 {Γ G M : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [Group G] [AddCommGroup M] [DistribMulAction G M]
    [DistribMulAction Γ M] (act : Γ →* G) (H : Subgroup Γ)
    (hact : ∀ (g : ↥H) (m : M), g • m = act (g : Γ) • m)
    (b : Γ → M) (hbZ : b ∈ Work.AbsoluteKummer.Z1 Γ M)
    (hmem : ((Work.SSGRoute.PT.H2Fin.resZ1 H M ⟨b, hbZ⟩ : Work.AbsoluteKummer.Z1 ↥H M) :
      ↥H → M) ∈ Work.AbsoluteKummer.B1 ↥H M) :
    SSGRoute.IsCoboundaryOn act H b := by
  rw [Work.AbsoluteKummer.mem_B1_iff] at hmem
  obtain ⟨m, hm⟩ := hmem
  refine ⟨m, fun g hg => ?_⟩
  have h1 := congrFun hm ⟨g, hg⟩
  rw [Work.GroupCohomology.d0_apply, hact ⟨g, hg⟩ m] at h1
  exact h1.symm

end

section Assembly

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]

/-- **The assembly step.**  If the `E1c` class of the canonical global dictionary class of `b`
restricts to zero on the involution group `⟨c⟩`, then `b|⟨c⟩` is a coboundary.

This is the formal inverse of the computation in
`ArchDictionary/archDictCoboundaryImpLocalZero` (`hcls` there), and the last step of the target. -/
theorem archDict_resH1_zpowers_eq_zero_imp_coboundary (p : ℕ) [Fact p.Prime] (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hMfinZ : Module.Finite ℤ ↑(Eprime p k Ω K T E)]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1)
    (b : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hl : SSGRoute.IsLocConstOn ⊤ b)
    (h : Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers c)
      (Work.SSGRoute.homCoind k Ω K (Eprime p k Ω K T E))
      (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K)
        (Eprime p k Ω K T E)
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = 0) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b := by
  classical
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  haveI hMfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  have hbZ : b ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) E :=
    Work.SSGRoute.mem_absZ1_of_isCocycleOn_isLocConstOn (SSGRoute.res k K) hb hl
  let 𝓔 : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) := Eprime p k Ω K T E
  let Φd := Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E
  have hΦd : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Φd.toAddMonoidHom :=
    fun σ e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E σ e
  have hΦd' : Work.GroupCohomology.IsEquivariant (↥(Subgroup.zpowers c)) Φd.toAddMonoidHom :=
    fun g e => Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E g e
  have hcls : Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) 𝓔
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)
      = (Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦd
          (fun σ n =>
            Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E σ n))
          (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩) := by
    have h1 : Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b
        = (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) 𝓔).symm
            ((Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦd
              (fun σ n =>
                Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E σ n))
              (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩)) := by
      rw [show Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b
          = Work.SSGRoute.E1aClean.globalDictEquivCanon p k Ω K ζ hζ hζK T hT E
              (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩) from by
        dsimp only [Work.SSGRoute.E1aClean.globalDictionaryCanon]
        exact dif_pos hbZ]
      show ((Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦd
            (fun σ n =>
              Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E σ n)).trans
              (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) 𝓔).symm)
          (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩) = _
      rw [AddEquiv.trans_apply]
    rw [h1]
    exact AddEquiv.apply_symm_apply (Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := k) (Ω := Ω) (K := K) 𝓔)
      ((Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦd
        (fun σ n =>
          Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E σ n))
        (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) E ⟨b, hbZ⟩))
  rw [hcls] at h
  rw [show ⇑(Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦd
        (fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E σ n))
      = ⇑(Work.AbsoluteKummer.mapH1 Φd.toAddMonoidHom hΦd) from rfl] at h
  rw [resH1_mapH1 (Nsub := Subgroup.zpowers c) (θ := Φd.toAddMonoidHom) hΦd hΦd'] at h
  rw [Work.SSGRoute.PT.H2Fin.resH1_H1π] at h
  have hΦd'' : Work.GroupCohomology.IsEquivariant (↥(Subgroup.zpowers c))
      Φd.symm.toAddMonoidHom :=
    fun g n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E g n
  have hB1 : (((Work.SSGRoute.PT.H2Fin.resZ1 (Subgroup.zpowers c) E) ⟨b, hbZ⟩ :
      Work.AbsoluteKummer.Z1 ↥(Subgroup.zpowers c) E) : ↥(Subgroup.zpowers c) → E)
      ∈ Work.AbsoluteKummer.B1 ↥(Subgroup.zpowers c) E := by
    refine (Work.AbsoluteKummer.H1π_eq_zero_iff _).mp ?_
    refine ((Work.SSGRoute.H1Equiv.h1AddEquiv (G := ↥(Subgroup.zpowers c)) Φd hΦd' hΦd'').injective) ?_
    rw [show ⇑(Work.SSGRoute.H1Equiv.h1AddEquiv (G := ↥(Subgroup.zpowers c)) Φd hΦd' hΦd'')
        = ⇑(Work.AbsoluteKummer.mapH1 Φd.toAddMonoidHom hΦd') from rfl]
    rw [map_zero]
    exact h
  exact isCoboundaryOn_of_mem_B1 (SSGRoute.res k K) (Subgroup.zpowers c)
    (fun g m => rfl) b hbZ hB1

end Assembly

section Odd

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]

/-- **The target for odd `p`.**  Every `1`-cocycle on the involution group `⟨c⟩` is a coboundary
(`AcOdd.isCoboundaryOn_of_odd`), so the localisation hypothesis is not needed at all. -/
theorem archDict_localZero_imp_coboundary_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1)
    (b : (Ω ≃ₐ[k] Ω) → E) (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b := by
  haveI : Normal k ↥K := IsGalois.to_normal
  exact isCoboundaryOn_of_odd (K := K) (p := p) (E := E) hp c hc2 b
    (IsCocycleOn.mono (H := Subgroup.zpowers c) (H' := ⊤) le_top hb)

end Odd

section Two

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]

/-- The `μ₂`-lift to `Ωˣ` of an element of `ℂˣ`: `1 ↦ 1`, everything else `↦ -1`. -/
noncomputable def liftMu2 (Ω : Type) [Field Ω] (v : ℂˣ) : Ωˣ := if v = 1 then 1 else -1

/-- `liftMu2` is a section of `φ` on the `2`-torsion of `ℂˣ`. -/
theorem map_liftMu2 {Ω : Type} [Field Ω] (φ : Ω →+* ℂ) (v : ℂˣ) (hv : v ^ 2 = 1) :
    Units.map φ.toMonoidHom (liftMu2 Ω v) = v := by
  rcases eq_or_ne v 1 with h | h
  · rw [liftMu2, if_pos h, map_one, h]
  · have hv1 : v = -1 := by
      have h2 : ((v : ℂ)) ^ 2 = 1 := by
        have := congrArg (fun u : ℂˣ => (u : ℂ)) hv
        simpa using this
      rcases sq_eq_one_iff.mp h2 with h' | h'
      · exact absurd (Units.ext h') h
      · exact Units.ext h'
    rw [liftMu2, if_neg h, hv1]
    rw [← Units.val_eq_neg_one, Units.coe_map, Units.coe_neg_one]
    show (φ (-1) : ℂ) = -1
    rw [map_neg, map_one]

/-- The values of `liftMu2` are `2`-torsion. -/
theorem liftMu2_sq (Ω : Type) [Field Ω] (v : ℂˣ) : (liftMu2 Ω v) ^ 2 = 1 := by
  rcases eq_or_ne v 1 with h | h
  · rw [liftMu2, if_pos h]; exact one_pow 2
  · rw [liftMu2, if_neg h, pow_two, neg_mul, one_mul, neg_neg]

/-- `liftMu2` is multiplicative on the `2`-torsion of `ℂˣ`. -/
theorem liftMu2_mul {Ω : Type} [Field Ω] (φ : Ω →+* ℂ) {a b : ℂˣ} (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) : liftMu2 Ω (a * b) = liftMu2 Ω a * liftMu2 Ω b := by
  have hinj : Function.Injective (Units.map φ.toMonoidHom) := by
    intro x y hxy
    apply Units.ext
    apply φ.injective
    have := congrArg (fun u : ℂˣ => (u : ℂ)) hxy
    simpa [Units.coe_map] using this
  apply hinj
  rw [map_mul, map_liftMu2 φ (a * b) (by rw [mul_pow, ha, hb, one_mul]),
    map_liftMu2 φ a ha, map_liftMu2 φ b hb]

/-- **The target at `p = 2`**: the arithmetic case. -/
theorem archDict_localZero_imp_coboundary_two (p : ℕ) [Fact p.Prime] (hp : p = 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (w : NK.GlobalCFT.Place ↥K) (φ : Ω →+* ℂ)
    (hwinf : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥)
    (b : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hl : SSGRoute.IsLocConstOn ⊤ b)
    (hγ : SSGRoute.PTExt.extLoc (k := k) w
      (SSGRoute.PTExt.extToIdeles (k := k)
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = 0) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b := by
  sorry

end Two

theorem archDict_localZero_imp_coboundary (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (w : NK.GlobalCFT.Place ↥K) (φ : Ω →+* ℂ)
    (hwinf : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥)
    (b : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hl : SSGRoute.IsLocConstOn ⊤ b)
    (hγ : SSGRoute.PTExt.extLoc (k := k) w
      (SSGRoute.PTExt.extToIdeles (k := k)
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = 0) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b := by
  by_cases hp : p = 2
  · -- the arithmetic case `p = 2`
    exact archDict_localZero_imp_coboundary_two p hp k Ω K ζ hζ hζK T hT E c hc2 hc1 w φ
      hwinf hw hlink hne b hb hl hγ
  · exact archDict_localZero_imp_coboundary_odd p hp k Ω K E c hc2 b hb

end Work.SSGRoute.ArchDictionary
