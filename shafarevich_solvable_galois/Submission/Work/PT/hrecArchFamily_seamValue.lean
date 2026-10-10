import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.PT.archFamily_zpowers_eq_zero_of_ne_two
import Submission.Work.SSGRoute.PT.G1plusOwn.levelPairPushLocal
import Submission.Work.SSGRoute.PT.archPairLocalAbs_hpairArch
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option maxHeartbeats 1000000

namespace Work.PT

/-- **The archimedean seam square in the `finZBg` spelling.**  `PT.archβc_square` states the
identity for the abstract global dictionary `PT.archβg` of `localDictionary_natural_family_arch`;
`PT.finZBg` is *definitionally* that same `Classical.choose`, so the clause transfers verbatim. -/
theorem finZBg_square_archβc (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (b : (Ω ≃ₐ[k] Ω) → M)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hl : SSGRoute.IsLocConstOn ⊤ b) :
    SSGRoute.PTExt.extLoc (k := k) (Work.SSGRoute.PT.archW k Ω K φ)
        (SSGRoute.PTExt.extToIdeles (k := k) (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M b))
      = Work.SSGRoute.PT.archβc p k Ω K ζ hζ hζK T hT M c (Work.SSGRoute.PT.archW k Ω K φ) b :=
  Work.SSGRoute.PT.archβc_square p k Ω K ζ hζ hζK T hT M c hc2 hc1 φ hφ b hb hl

/-- **For odd `p` the archimedean value vanishes when the first argument is a coboundary on `⟨c⟩`:**
`archβc c a = 0` by `PT.archβc_eq_zero_iff`, and then `levelPair` and `ι` and `χ` kill `0`.  This is
the odd-`p` half of the seam value formula (`2` is invertible in `𝔽_p`, so *every* `1`-cocycle on
the two-element group `⟨c⟩` with coefficients in a `ZMod p`-module is a coboundary, whence the value
is `0` for *every* `a` — see `PT.archFamily_zpowers_eq_zero_of_ne_two`). -/
theorem archPairValueZ_eq_zero_of_isCoboundaryOn (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a : (Ω ≃ₐ[k] Ω) → M) (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a)
    (hcob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) a)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (Work.SSGRoute.PT.archW k Ω K φ))
    (z : SSGRoute.PTExt.extH (Rep.res (Work.SSGRoute.decompKRestrict k (↥K) (↥L)
        (Work.SSGRoute.PT.archW k Ω K φ) u hu)
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (Work.SSGRoute.PT.archW k Ω K φ)).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))) 1) :
    Work.SSGRoute.PT.archPairValueZ p k Ω K ζ hζ hζK T hT χ M c
      (Work.SSGRoute.PT.archW k Ω K φ) a L hKL u hu z = 0 := by
  rw [Work.SSGRoute.PT.archPairValueZ,
    (Work.SSGRoute.PT.archβc_eq_zero_iff p k Ω K ζ hζ hζK T hT M c hc2 hc1 φ hφ a ha).mpr hcob,
    Work.SSGRoute.levelPair_zero, Work.SSGRoute.PT.pt_iota_zero]
  exact Work.SSGRoute.PT.chi_zero p k Ω K χ hχadd L hKL

theorem hrecArchFamily_seamValue
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
      [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
      (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (φc : (c : Ω ≃ₐ[k] Ω) → c ^ 2 = 1 → c ≠ 1 → Ω →+* ℂ)
    (hφc : ∀ (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (x : Ω),
      φc c hc2 hc1 (c x) = starRingEnd ℂ (φc c hc2 hc1 x))
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.PT.VFcoef p M T)
    (ha1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a) (ha2 : SSGRoute.IsLocConstOn ⊤ a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L)
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.PT.VFcoef p M T)
    (hfac : ∀ σ : Ω ≃ₐ[k] Ω, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (hψ : ∀ g h : ↥L ≃ₐ[k] ↥L,
      b₀ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • b₀ h + b₀ g) :
    Work.SSGRoute.PT.archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a b =
      χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
        (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
          ((φc c hc2 hc1).comp (algebraMap ↥L Ω))))
        (SSGRoute.PTExt.extLoc (k := k) (K := ↥L)
          (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
            ((φc c hc2 hc1).comp (algebraMap ↥L Ω))))
          (SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k (↥K) (↥L))
            (Work.SSGRoute.idleRepMap k (↥K) (↥L))
            (SSGRoute.PTExt.extToIdeles (k := k)
              (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a))
            (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀ hψ)))) := by
  classical
  -- `a` is a cocycle on `⟨c⟩` because it is one on all of `G_k`.
  have ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a :=
    fun g _ h _ => ha1 g trivial h trivial
  -- `hfac` restricts to the hypothesis `hres` of the local value formula.
  have hres : ∀ σ ∈ Subgroup.zpowers c, b σ = b₀ (SSGRoute.res k L σ) :=
    fun σ _ => hfac σ
  have hu : NK.GlobalCFT.Place.LiesOver
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        ((φc c hc2 hc1).comp (algebraMap ↥L Ω))))
      (Work.SSGRoute.PT.archW k Ω K (φc c hc2 hc1)) :=
    Work.SSGRoute.PT.liesOver_linked k Ω K L (φc c hc2 hc1)
  -- The localisation of `finZBg` at the linked place is the seam dictionary `archβc`.
  have hsquare : SSGRoute.PTExt.extLoc (k := k) (Work.SSGRoute.PT.archW k Ω K (φc c hc2 hc1))
      (SSGRoute.PTExt.extToIdeles (k := k) (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a))
      = Work.SSGRoute.PT.archβc p k Ω K ζ hζ hζK T hT M c
          (Work.SSGRoute.PT.archW k Ω K (φc c hc2 hc1)) a :=
    finZBg_square_archβc p k Ω K ζ hζ hζK T hT M c hc2 hc1 (φc c hc2 hc1)
      (hφc c hc2 hc1) a ha1 ha2
  -- The right-hand side in the global spelling localises, by `levelPairPushLocal`, to the local
  -- `levelPair` with `archβc`.
  have hbridge : SSGRoute.PTExt.extLoc (k := k) (K := ↥L)
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        ((φc c hc2 hc1).comp (algebraMap ↥L Ω))))
      (SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k (↥K) (↥L))
        (Work.SSGRoute.idleRepMap k (↥K) (↥L))
        (SSGRoute.PTExt.extToIdeles (k := k) (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a))
        (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀ hψ))
      = SSGRoute.PTExt.levelPair
          (Work.SSGRoute.decompKRestrict k (↥K) (↥L)
            (Work.SSGRoute.PT.archW k Ω K (φc c hc2 hc1))
            (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
              ((φc c hc2 hc1).comp (algebraMap ↥L Ω)))) hu)
          (Work.SSGRoute.localUnitsMap k (↥K) (↥L)
            (Work.SSGRoute.PT.archW k Ω K (φc c hc2 hc1))
            (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
              ((φc c hc2 hc1).comp (algebraMap ↥L Ω)))) hu)
          (Work.SSGRoute.PT.archβc p k Ω K ζ hζ hζK T hT M c
            (Work.SSGRoute.PT.archW k Ω K (φc c hc2 hc1)) a)
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
              ((φc c hc2 hc1).comp (algebraMap ↥L Ω)))))
            (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀ hψ)) := by
    rw [← Work.SSGRoute.PT.G1plusOwn.levelPairPushLocal k (↥K) (↥L)
      (SSGRoute.PTExt.extToIdeles (k := k) (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a))
      (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀ hψ)
      (Work.SSGRoute.PT.archW k Ω K (φc c hc2 hc1))
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        ((φc c hc2 hc1).comp (algebraMap ↥L Ω)))) hu]
    rw [hsquare]
  by_cases hp2 : p = 2
  · -- ## `p = 2`: the value formula at the involution, at the level `L`
    rw [Work.SSGRoute.PT.archFamily_zpowers p k Ω K ζ hζ hζK T hT χ φc hφc M c hc2 hc1 a b]
    rw [← Work.SSGRoute.PT.archPairLocalAbs_archβc p k Ω K ζ hζ hζK T hT χ M c hc2 hc1
      (φc c hc2 hc1) (hφc c hc2 hc1) a b]
    rw [Work.SSGRoute.PT.archPairLocalAbs_hpairArch_two p hp2 k Ω K ζ hζ hζK T hT
      (Work.SSGRoute.PT.archβcSeam p k Ω K ζ hζ hζK T hT) χ hχadd hχcompat M c hc2 hc1 a b
      ha hb (φc c hc2 hc1) (hφc c hc2 hc1) L hKL
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        ((φc c hc2 hc1).comp (algebraMap ↥L Ω)))) hu rfl b₀ hψ hres]
    refine Eq.trans (Work.SSGRoute.PT.archPairValueZAbs_archβc p k Ω K ζ hζ hζK T hT χ M c
      (Work.SSGRoute.PT.archW k Ω K (φc c hc2 hc1)) a L hKL
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        ((φc c hc2 hc1).comp (algebraMap ↥L Ω)))) hu
      (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
          ((φc c hc2 hc1).comp (algebraMap ↥L Ω)))))
        (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀ hψ))) ?_
    rw [hbridge]
    rfl
  · -- ## `p ≠ 2`: both sides vanish (`H¹(C₂, -) = H²(C₂, -) = 0` since `2` is invertible mod `p`)
    rw [Work.PT.archFamily_zpowers_eq_zero_of_ne_two p hp2 k Ω K ζ hζ hζK T hT χ hχadd φc hφc M
      c hc2 a b ha hb]
    rw [hbridge]
    exact (archPairValueZ_eq_zero_of_isCoboundaryOn p k Ω K ζ hζ hζK T hT χ hχadd M c hc2 hc1
      (φc c hc2 hc1) (hφc c hc2 hc1) a ha
      (Work.SSGRoute.ArchAux.isCoboundaryOn_of_isCocycleOn_of_ne_two p hp2 (SSGRoute.res k K)
        c hc2 a ha)
      L hKL
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        ((φc c hc2 hc1).comp (algebraMap ↥L Ω)))) hu
      (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
          ((φc c hc2 hc1).comp (algebraMap ↥L Ω)))))
        (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀ hψ))).symm

end Work.PT
