import Mathlib
import Submission.Work.SSGRoute.E1aClean.ArchCompare
import Submission.Work.SSGRoute.E1aClean.ArchSeam
import Submission.Work.SSGRoute.PT.freeCoverCompatKernel
import Submission.Work.SSGRoute.PT.e1cDelta_beta_relation_gen
import Submission.Work.SSGRoute.E1cGeneric.freeCoverCompat_comp
import Submission.Work.SSGRoute.E1cGeneric.freeCoverCompat_single
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000

namespace Work.SSGRoute.E1aClean

/- The two `AddCommGroup`/`Module` instances carried by a `Rep` are pinned at high priority so that
instance search does not pick a different (definitionally equal) structure when the free
representations `Rep.free Coeff G X.V` are compared across the two groups `Gal(K/k)` and
`localGroup`; this is the same device as in `homCoindDefs.lean`. -/
attribute [local instance 10000] Rep.hV1 Rep.hV2

/-- The place-change comparison `SES`-morphism of the archimedean local criterion: the two
commuting squares comparing the `⟨σ⟩`-restricted global dualised canonical resolution with the
local one at `(ℝ, ℂ, ⊤)`, through the seam coefficient change `seamCoeff φ`.  This is gap (iii) of
`E1aClean/NOTE_infLocalCriterion_frontier.md`; the middle/tail comparisons `u₂`, `u₃` are the
cover and syzygy comparisons. -/
theorem archimedeanComparisonSES_proved {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (w : NumberField.InfinitePlace ↥K) (hw : w.IsComplex)
    (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)))
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hres : SSGRoute.res k K σ = (τ : ↥K ≃ₐ[k] ↥K))
    (φ : Ω →+* ℂ)
    (hφK : ∀ y : ↥K, φ (algebraMap ↥K Ω y) = NumberField.InfinitePlace.embedding w y)
    (hlink : ∀ x : Ω, φ (σ x) = starRingEnd ℂ (φ x))
    (X : Rep.{0} SSGRoute.PTExt.Coeff (↥K ≃ₐ[k] ↥K)) [Finite X.V]
    [IsAlgClosure ℝ ℂ]
    [FiniteDimensional ℝ Work.SSGRoute.E1aClean.localLevel]
    [IsGalois ℝ Work.SSGRoute.E1aClean.localLevel]
    (Φ : ↥(Subgroup.zpowers σ) ≃* Work.SSGRoute.E1aClean.localGroup) :
    ∃ (u₂ : (Rep.free SSGRoute.PTExt.Coeff Work.SSGRoute.E1aClean.localGroup X.V).V →+
              (Rep.free SSGRoute.PTExt.Coeff (↥K ≃ₐ[k] ↥K) X.V).V)
      (u₃ : (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover
              (Work.SSGRoute.E1aClean.localX (k := k) (Ω := Ω) (K := K) σ X Φ))).V →+
              (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)).V),
      (∀ x : Work.SSGRoute.homCoind k Ω K X,
        (Work.SSGRoute.PT.e1aSESgen (k := ℝ) (Ω := ℂ) (K := Work.SSGRoute.E1aClean.localLevel)
            (Work.SSGRoute.E1aClean.localX (k := k) (Ω := Ω) (K := K) σ X Φ)).iota
            ((Work.SSGRoute.E1aClean.seamCoeff φ) x)
          = (Work.SSGRoute.E1aClean.seamCoeff φ)
              (((Work.SSGRoute.ExtChain.restrictSES
                  (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) X)
                  (Subgroup.zpowers σ)).iota x).comp u₂)) ∧
      (∀ y : Work.SSGRoute.ExtChain.homCoindFreeT k Ω K X.V,
        (Work.SSGRoute.PT.e1aSESgen (k := ℝ) (Ω := ℂ) (K := Work.SSGRoute.E1aClean.localLevel)
            (Work.SSGRoute.E1aClean.localX (k := k) (Ω := Ω) (K := K) σ X Φ)).pi
            ((Work.SSGRoute.E1aClean.seamCoeff φ) (y.comp u₂))
          = (Work.SSGRoute.E1aClean.seamCoeff φ)
              (((Work.SSGRoute.ExtChain.restrictSES
                  (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) X)
                  (Subgroup.zpowers σ)).pi y).comp u₃)) := by
  classical
  -- The local module at the archimedean data `(ℝ, ℂ, ⊤)`, transported along `Φ`.
  let ℓ : Rep.{0} SSGRoute.PTExt.Coeff Work.SSGRoute.E1aClean.localGroup :=
    Work.SSGRoute.E1aClean.localX (k := k) (Ω := Ω) (K := K) σ X Φ
  -- **The cover comparison `u₂`**: the canonical cover of `X` is surjective, and the underlying
  -- `ℤ`-module of the free representation on the local side is free, hence projective; lift the
  -- local cover `freeCover ℓ` along `freeCover X`.
  obtain ⟨u₂l, hu₂l⟩ := Module.projective_lifting_property
    (R := SSGRoute.PTExt.Coeff)
    (f := (Rep.Hom.hom (Work.SSGRoute.freeCover X)).toLinearMap)
    (g := (Rep.Hom.hom (Work.SSGRoute.freeCover ℓ)).toLinearMap)
    (show Function.Surjective (Rep.Hom.hom (Work.SSGRoute.freeCover X)).toLinearMap from
      Work.SSGRoute.freeCover_surjective X)
  -- Its defining property, at the level of `AddMonoidHom`s: it intertwines the two covers.
  have hcu₂ : (Rep.Hom.hom (Work.SSGRoute.freeCover X)).toAddMonoidHom.comp u₂l.toAddMonoidHom
      = (Rep.Hom.hom (Work.SSGRoute.freeCover ℓ)).toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro v
    exact congrArg (fun w => w v) hu₂l
  -- The local kernel inclusion lands in the kernel of the local cover (the kernel condition).
  have hclcl' : ∀ w : (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover ℓ)).V,
      (Rep.Hom.hom (Work.SSGRoute.freeCover ℓ)).toAddMonoidHom
        ((Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover ℓ))).toAddMonoidHom w) = 0 := by
    intro w
    have hcond := congrArg
      (fun (m : CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover ℓ) ⟶ ℓ) => (Rep.Hom.hom m) w)
      (CategoryTheory.Limits.kernel.condition (Work.SSGRoute.freeCover ℓ))
    simpa [Rep.hom_comp, Rep.zero_hom] using hcond
  -- **The syzygy comparison `u₃`**: the composite `u₂ ∘ (kernel inclusion)` lands in the kernel of
  -- the global cover, i.e. in the range of the global kernel inclusion.
  have hrange : ∀ w : (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover ℓ)).V,
      u₂l.toAddMonoidHom
        ((Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover ℓ))).toAddMonoidHom w)
      ∈ ((Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover X))).toAddMonoidHom).range := by
    intro w
    rw [← ker_hom_eq_range_kernel_iota (k := k) (K := K) (freeCover X), AddMonoidHom.mem_ker]
    have h1 : (Rep.Hom.hom (Work.SSGRoute.freeCover X)).toAddMonoidHom
        (u₂l.toAddMonoidHom
          ((Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover ℓ))).toAddMonoidHom w)) = 0 := by
      rw [← AddMonoidHom.comp_apply, hcu₂]
      exact hclcl' w
    exact h1
  have hmono : Function.Injective
      (Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover X))).toAddMonoidHom :=
    (Rep.mono_iff_injective (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover X))).mp inferInstance
  -- The kernel inclusion is injective, so the chosen preimages assemble into an additive map.
  let u₃ : (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover ℓ)).V →+
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)).V :=
    { toFun := fun w => Classical.choose (hrange w)
      map_zero' := by
        apply hmono
        rw [Classical.choose_spec (hrange 0)]
        simp
      map_add' := by
        intro a b
        apply hmono
        rw [Classical.choose_spec (hrange (a + b))]
        rw [map_add ((Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover ℓ))).toAddMonoidHom)]
        rw [map_add u₂l.toAddMonoidHom]
        rw [map_add ((Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover X))).toAddMonoidHom)]
        rw [Classical.choose_spec (hrange a), Classical.choose_spec (hrange b)] }
  have hu₃ : (Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover X))).toAddMonoidHom.comp u₃
      = u₂l.toAddMonoidHom.comp (Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover ℓ))).toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro w
    exact Classical.choose_spec (hrange w)
  refine ⟨u₂l.toAddMonoidHom, u₃, ?_, ?_⟩
  · -- the `ι`-square: both sides are `seamCoeff φ x` precomposed with the two covers, and
    -- `freeCover X ∘ u₂ = freeCover ℓ`.
    intro x
    rw [Work.SSGRoute.PT.e1aSESgen_iota]
    rw [Work.SSGRoute.ExtChain.restrictSES_iota, Work.SSGRoute.PT.e1aSESgen_iota]
    simp only [Work.SSGRoute.precompAddHom_apply]
    simp only [Work.SSGRoute.E1aClean.seamCoeff_precomp]
    simp only [AddMonoidHom.comp_assoc]
    rw [hcu₂]
  · -- the `π`-square: both sides are `seamCoeff φ y` precomposed with the two kernel inclusions,
    -- and `kernel.ι (freeCover X) ∘ u₃ = u₂ ∘ kernel.ι (freeCover ℓ)`.
    intro y
    rw [Work.SSGRoute.PT.e1aSESgen_pi]
    rw [Work.SSGRoute.ExtChain.restrictSES_pi, Work.SSGRoute.PT.e1aSESgen_pi]
    simp only [Work.SSGRoute.precompAddHom_apply]
    simp only [Work.SSGRoute.E1aClean.seamCoeff_precomp]
    simp only [AddMonoidHom.comp_assoc]
    rw [hu₃]

end Work.SSGRoute.E1aClean
