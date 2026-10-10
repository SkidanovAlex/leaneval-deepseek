import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.G1plusLevel.finLevelClass_eq_zero_of_eq_d0
import Submission.Work.SSGRoute.PT.G1plusLevelClauses
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped TensorProduct

namespace Work.SSGRoute.PT.G1plusLevel

/-! ## The ingredients of clause (3), second variable, for the finite half

`PT.finAtLevel` is `χ L hKL (ι_w (levelPair f ι (βl a) [b]_L))`, so the `b`-side of clause (3)
(`finAtLevel … a b … = 0` for `b` a coboundary on `decomp k A`) is the statement that the *level
class* `[b]_L = finZH …` vanishes: `[b]_L` is the `Ext¹`-class of the `1`-cocycle
`g ↦ b₀ (g : L ≃ₐ[k] L)` on `D_w`, and a coboundary on `decomp k A` restricts to a coboundary on
`D_w` (`res k L : decomp k A →* D_w` is onto, `finQW_glue`).

* `finZF_coboundary_witness` — the level-free bookkeeping: the witness `m` of the coboundary on
  `decomp k A` is also a witness on `D_w`, for the action pulled back along the place glue `finZF`;
* `finZH_eq_zero_of_isCoboundaryOn` — the level class of such a `b` vanishes, i.e.
  `[b₀|D_w] = 0` in `H¹(D_w, M^∨(1))` (via the proved `finLevelClass_eq_zero_of_eq_d0`). -/

/-- **Level-free coboundary witness for the factorised cocycle.**

If `b` is a `1`-coboundary on the decomposition group `decomp k A` of a finite place `A` (with
witness `m`), and `b₀` factorises `b|decomp k A` through `Gal(L/k)`, then the restriction of `b₀`
to the decomposition group `D_w` of the place of `L` under `A` is the coboundary of the *same*
witness `m` for the action pulled back along the place glue `finZF`.

The content is that `res k L : decomp k A →* D_w` is onto (`PT.finQW_glue`) and that
`galRes k K L (res k L σ) = res k K σ` (`SSGRoute.PTExt.galRes_trans`), combined with
`PT.finZF_spec`. -/
theorem finZF_coboundary_witness (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (b₀ : (↥L ≃ₐ[k] ↥L) → SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (hcob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b) :
    ∃ m : SSGRoute.DualMod p (M ⊗[ZMod p] T),
      ∀ g : ↥(SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite (finQW L A hA))),
        b₀ (g : ↥L ≃ₐ[k] ↥L)
          = ((finZF hKL A hA g :
                ↥(SSGRoute.PTExt.decompK (k := k)
                  (NK.GlobalCFT.Place.ofFinite (finQ K A hA)))) : ↥K ≃ₐ[k] ↥K) • m - m := by
  obtain ⟨m, hm⟩ := hcob
  refine ⟨m, fun g => ?_⟩
  -- `g` is the restriction of some `σ ∈ decomp k A`
  have hg : (g : ↥L ≃ₐ[k] ↥L) ∈ Subgroup.map (SSGRoute.res k L) (SSGRoute.decomp k A) := by
    rw [finQW_glue L A hA]; exact g.2
  obtain ⟨σ, hσ, hσeq⟩ := Subgroup.mem_map.mp hg
  -- the group element of `finZF` at `g` is `res k K σ`
  have hcoe : ((finZF hKL A hA g :
        ↥(SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite (finQ K A hA)))) : ↥K ≃ₐ[k] ↥K)
      = SSGRoute.res k K σ := by
    rw [finZF_spec hKL A hA g, ← hσeq]
    exact SSGRoute.PTExt.galRes_trans σ
  rw [hcoe, ← hσeq, ← hb₀ σ hσ]
  exact hm σ hσ

/-- **The level class `[b]_L` vanishes when `b` is a coboundary on `decomp k A`.**

This is the `finZH`-spelling of clause (3), second variable, at a fixed level: the second factor of
`finZZ = levelPair finZF finZI (finZB a) (finZH …)` is `0`, so the level pairing is `0` and the
clause follows from `χ`'s vanishing at `0` (`PT.chi_zero`). -/
theorem finZH_eq_zero_of_isCoboundaryOn (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (b₀ : (↥L ≃ₐ[k] ↥L) → SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (hcob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b) :
    finZH p K T M L hKL A hA b hb b₀ hb₀ = 0 := by
  obtain ⟨m, hm⟩ := finZF_coboundary_witness p k Ω K T M L hKL A hA b b₀ hb₀ hcob
  rw [finZH]
  refine finLevelClass_eq_zero_of_eq_d0 (q := finQ K A hA) (w := finQW L A hA)
    (f := finZF hKL A hA) (hf := finZF_spec hKL A hA) (b₀ := b₀)
    (hcrossed := factorised_isCrossedHom p k Ω K L hKL A hA (finQ K A hA)
      (fun x => finQ_spec K A hA x) (finQW L A hA) (fun y => finQW_spec L A hA y)
      (finQW_glue L A hA) (SSGRoute.DualMod p (M ⊗[ZMod p] T)) b hb b₀ hb₀)
    (m := m) (hm := hm)

/-- **Clause (3) of `G1⁺`'s finite half at a fixed level, second variable**: `finAtLevel` vanishes
when its second argument `b` is a coboundary on the decomposition group of `A`.  (The analogue of
`PT.finAtLevel_coboundary_left` on the `b`-side: the level class `finZH` dies, and the level
pairing dies with it.) -/
theorem finAtLevel_coboundary_right (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
        K ≤ L → SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2 → ZMod p)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
        p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (b₀ : (↥L ≃ₐ[k] ↥L) → SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (hcob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b) :
    finAtLevel p k Ω K ζ hζ hζK T hT χ M A hA L hKL a b hb b₀ hb₀ = 0 := by
  classical
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
  haveI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hZH : finZH p K T M L hKL A hA b hb b₀ hb₀ = 0 :=
    finZH_eq_zero_of_isCoboundaryOn p k Ω K T M L hKL A hA b hb b₀ hb₀ hcob
  simp only [finAtLevel, finZZ]
  rw [hZH, Work.SSGRoute.levelPair_zero_h, pt_iota_zero]
  exact chi_zero p k Ω K χ hχadd L hKL

/-- **Clause (3) of the finite half, second variable, level-free**: `finAtValue` vanishes when its second argument `b` is a coboundary (on the decomposition group of `A`).  Level-free because `finAtValue` chooses its level from `b` alone.  This is the third conjunct of `H1Pair.PairClauses` for the finite half (`hclauses` of `G1⁺`) on the `b`-side. -/
theorem finAtValue_coboundary_right (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
        K ≤ L → SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2 → ZMod p)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
        p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (hb : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hcob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b) :
    Work.SSGRoute.PT.finAtValue p k Ω K ζ hζ hζK T hT χ M A hA (SSGRoute.decomp k A) a b ha hb
      = 0 := by
  classical
  simp only [finAtValue]
  rw [dif_pos trivial]
  by_cases hbc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b
  · rw [dif_pos hbc]
    -- the level chosen by `finAtValue` (from `b` alone, never from `a`)
    have hL := exists_level_factors_locConstOn p k Ω K
      (M := DualMod p (M ⊗[ZMod p] T)) (SSGRoute.decomp k A) b hb
    let L := hL.choose
    have hLfin : FiniteDimensional k L := hL.choose_spec.choose
    have hLnorm : Normal k L := hL.choose_spec.choose_spec.choose
    letI : FiniteDimensional k L := hLfin
    letI : Normal k L := hLnorm
    letI : IsGalois k L := inferInstance
    letI : NumberField L := inferInstance
    have hKL : K ≤ L := hL.choose_spec.choose_spec.choose_spec.1
    have hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ =
        hL.choose_spec.choose_spec.choose_spec.2.choose
          (AlgEquiv.restrictNormalHom L σ) :=
      hL.choose_spec.choose_spec.choose_spec.2.choose_spec
    exact finAtLevel_coboundary_right p k Ω K ζ hζ hζK T hT χ hχadd M A hA L hKL a b hbc
      (hL.choose_spec.choose_spec.choose_spec.2.choose) hb₀ hcob
  · rw [dif_neg hbc]

end Work.SSGRoute.PT.G1plusLevel
