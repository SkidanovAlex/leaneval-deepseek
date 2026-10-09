import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.PT.decompK_linked
import Submission.Work.SSGRoute.LTDArch.AuxLemmas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Setting lemmas for the split (real) archimedean place

Extracted verbatim from `ArchDictionary/archimedeanDictSplitPlace.lean` (which now imports this
module) so that the delegated pieces of `archimedeanDictSplitPlace` can be stated and proved in
files that do not import the still-sorried target statement.

* `res_eq_one_of_decompK_eq_bot`: at a place with trivial decomposition group, the seam involution
  `c` acts trivially on `K`;
* the `⟨c⟩`-cocycle/`⟨c⟩`-coboundary normal forms for a trivially acting `c`;
* the two seam sign lemmas (`φ z` real when `c z = z`, purely imaginary when `c z = -z`).
-/

namespace Work.SSGRoute.ArchDictionary

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]

/-- At a place with trivial decomposition group the involution `c` fixes `K`. -/
theorem res_eq_one_of_decompK_eq_bot (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (φ : Ω →+* ℂ) (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hbot : SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω)))) = ⊥) :
    SSGRoute.res k K c = 1 := by
  have h := Work.SSGRoute.PT.decompK_linked k Ω K c hc2 hc1 φ hlink
  rw [h] at hbot
  have hmem : SSGRoute.res k K c ∈ (Subgroup.zpowers c).map (SSGRoute.res k K) :=
    ⟨c, Subgroup.mem_zpowers c, rfl⟩
  rw [hbot] at hmem
  simpa using hmem

/-- The `⟨c⟩`-cocycles, when `c` acts trivially on `K`. -/
theorem isCocycleOn_zpowers_iff_of_res_eq_one {E : Type} [AddCommGroup E]
    [DistribMulAction (K ≃ₐ[k] K) E] (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1)
    (hres : SSGRoute.res k K c = 1) (b : (Ω ≃ₐ[k] Ω) → E) :
    SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ↔
      b 1 = 0 ∧ b c + b c = 0 := by
  rw [Work.SSGRoute.Ach.isCocycleOn_zpowers_iff (SSGRoute.res k K) c hc2 b, hres,
    one_smul]

/-- The `⟨c⟩`-coboundaries, when `c` acts trivially on `K`. -/
theorem isCoboundaryOn_zpowers_iff_of_res_eq_one {E : Type} [AddCommGroup E]
    [DistribMulAction (K ≃ₐ[k] K) E] (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1)
    (hres : SSGRoute.res k K c = 1) (b : (Ω ≃ₐ[k] Ω) → E) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b ↔
      b 1 = 0 ∧ b c = 0 := by
  rw [Work.SSGRoute.Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc2 b, hres]
  constructor
  · rintro ⟨h1, m, hm⟩
    exact ⟨h1, by rw [hm, one_smul, sub_self]⟩
  · rintro ⟨h1, hc⟩
    exact ⟨h1, 0, by rw [hc, one_smul, sub_self]⟩

/-- The fixed part of `Ω` under the seam involution maps into `ℝ`. -/
theorem phi_mem_real_of_fixed (φ : Ω →+* ℂ) (c : Ω ≃ₐ[k] Ω)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) {z : Ω} (hz : c z = z) :
    (φ z).im = 0 := by
  have h : starRingEnd ℂ (φ z) = φ z := by
    rw [← hlink z, hz]
  have h2 : -(φ z).im = (φ z).im := by simpa using congrArg Complex.im h
  linarith

/-- If `z` is anti-fixed by the seam involution, then `φ z` is purely imaginary. -/
theorem phi_re_eq_zero_of_anti_fixed (φ : Ω →+* ℂ) (c : Ω ≃ₐ[k] Ω)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) {z : Ω} (hz : c z = -z) :
    (φ z).re = 0 := by
  have h : starRingEnd ℂ (φ z) = -φ z := by
    rw [← hlink z, hz, map_neg]
  have h2 : (φ z).re = -(φ z).re := by simpa using congrArg Complex.re h
  linarith

end Work.SSGRoute.ArchDictionary
