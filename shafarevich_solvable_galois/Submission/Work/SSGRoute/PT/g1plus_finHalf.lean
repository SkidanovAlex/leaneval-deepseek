import Mathlib
import Submission.Work.SSGRoute.PT.finHalfData
import Submission.Work.SSGRoute.PT.finZZ_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `G1⁺`: the finite-place half `fin` and its level independence

`PT.finAtValue` (the finite-place half of `G1⁺`) and `PT.finAtLevel_eq_of_le` (its level
independence).  All the level data and their transport lemmas live in
`Submission.Work.SSGRoute.PT.finHalfData`, and the level transport of the local class `finZZ`
(`Work.SSGRoute.PT.finZZ_eq`, the last gate of the level independence) in
`Submission.Work.SSGRoute.PT.finZZ_eq`.

**Both `finAtLevel_eq_of_le` and `finAtValue` are complete** (`#print axioms` is
`[propext, Classical.choice, Quot.sound]`).
-/

open scoped TensorProduct Pointwise
open SSGRoute.PTExt CategoryTheory

noncomputable section

namespace Work.SSGRoute.PT

section FinHalf

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)

/-- **The value of the finite-place half at a finite place `A`, at a *specified* admissible level
`L` with a specified factorisation `b₀` of `b|_H` through `Gal(L/k)`** (the design's
`χ_L (ι_w (levelPair (βl a) [b]))`). -/
noncomputable def finAtLevel
    (χ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
        K ≤ L → extH (classesK k L) 2 → ZMod p)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L)
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (b₀ : ((↥L ≃ₐ[k] ↥L) → DualMod p (M ⊗[ZMod p] T)))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)) : ZMod p := by
  classical
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
  haveI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact χ L hKL (iota (k := k) (L := ↥L) (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
    (finZZ p K ζ hζ hζK T hT M L hKL A hA a b hb b₀ hb₀))

/-- **Level independence of `finAtLevel`** — the crux: for a `χ` satisfying the *inflation
coherence* `hχ` (clause (3) of the coherent `p`-torsion invariant `χ`, proved for the actual `χ`
in `coherent_pTorsion_chi_k`), the value does not depend on the admissible level `L` (nor on the
chosen factorisation `b₀`, which is pinned on `decomp k A` by `hb₀`).  This is PING §3's
"genuinely new bookkeeping piece": `levelPair`'s level change (`levelPair_comp_extHMap`), the level
transport of `extLoc` (`E7cOmega.extLoc_push_ideleMap`), and `ι_w`'s
`Classical.choose`-independence (`PT.eq_iotaLift_of_spec`).

**`hχ` is necessary**: without it the statement is false (`χ`'s fibres at `L` and `L'` are then
independent; `χ ≡ 0` at `L` and `χ ≡ 1` at `L'` is a counterexample).

**Proof** (this is the old `CokerPT.finAtLevelFix_eq_of_le` in another spelling): after
`simp only [finAtLevel]` the value is `χ L hKL (iota (ofFinite (finQW L A hA)) (finZZ …))`, and the
`inflLevel`-coherence of `χ` together with the spine (`PT.iotaLift_idleRepMap`,
`PT.extToClasses_idleRepMap`) and the level transport of the class (`PT.finZZ_eq`) give the
result.  The `p`-torsion input is `PT.finZB`'s value being `ZMod p`-torsion in its first variable
(`E6Util.ext_nsmul_p_torsion_left`). -/
theorem finAtLevel_eq_of_le
    (χ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
        K ≤ L → extH (classesK k L) 2 → ZMod p)
    (hχ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
        [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
        (u : extH (classesK k L) 2),
        p • u = 0 → χ L' hKL' (inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (L L' : IntermediateField k Ω) [NumberField L] [NumberField L']
    [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional k L'] [IsGalois k L']
    (hKL : K ≤ L) (hKL' : K ≤ L') (hLL : L ≤ L')
    (b₀ : ((↥L ≃ₐ[k] ↥L) → DualMod p (M ⊗[ZMod p] T)))
    (b₀' : ((↥L' ≃ₐ[k] ↥L') → DualMod p (M ⊗[ZMod p] T)))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (hb₀' : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀' (AlgEquiv.restrictNormalHom L' σ)) :
    finAtLevel p k Ω K ζ hζ hζK T hT χ M A hA L hKL a b hb b₀ hb₀
      = finAtLevel p k Ω K ζ hζ hζK T hT χ M A hA L' hKL' a b hb b₀' hb₀' := by
  simp only [finAtLevel]
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
  haveI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra ↥K ↥L' := (IntermediateField.inclusion hKL').toAlgebra
  haveI : IsScalarTower k ↥K ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L' Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra ↥L ↥L' := (IntermediateField.inclusion hLL).toAlgebra
  haveI : IsScalarTower k ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥L ↥L' Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hw' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L A hA)) :=
    NK.GlobalCFT.Place.liesOver_ofFinite (finQW_liesOver A hA hLL)
  -- the `p`-torsion of the level class `finZZ` (it is `levelPair` of two `ZMod p`-torsion classes)
  have hptor : p • finZZ p K ζ hζ hζK T hT M L hKL A hA a b hb b₀ hb₀ = 0 := by
    have hX : ∀ x : DualMod p (M ⊗[ZMod p] T), p • x = 0 :=
      fun x => nsmul_eq_zero_of_zmod' p x
    have h1 : p • (finZB p K ζ hζ hζK T hT M A hA a) = 0 :=
      Work.SSGRoute.E6Util.ext_nsmul_p_torsion_left p hX _
    simp only [finZZ]
    rw [pt_levelPair_nsmul_fst, h1, Work.SSGRoute.levelPair_zero]
  -- the level transport of the local class (`Work.SSGRoute.PT.finZZ_eq`, proved in
  -- `Submission/Work/SSGRoute/PT/finZZ_eq.lean`)
  have hz' : finZZ p K ζ hζ hζK T hT M L' hKL' A hA a b hb b₀' hb₀'
      = extHMap (decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
          (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw')
        (finMU (K := K) A hA hLL)
        (finZZ p K ζ hζ hζK T hT M L hKL A hA a b hb b₀ hb₀) :=
    finZZ_eq (A := A) (hA := hA) (p := p) (ζ := ζ) (hζ := hζ) (hζK := hζK) (T := T)
      (hT := hT) (M := M) (hKL := hKL) (hKL' := hKL') (hLL := hLL) (a := a) (b := b)
      (hb := hb) (b₀ := b₀) (b₀' := b₀') (hb₀ := hb₀) (hb₀' := hb₀')
  -- the `p`-torsion of `ι_w` of the class, and the `χ`-coherence, finish the argument
  have hiota_nsmul : ∀ n : ℕ, n • iota (k := k) (L := ↥L)
        (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
        (finZZ p K ζ hζ hζK T hT M L hKL A hA a b hb b₀ hb₀)
      = iota (k := k) (L := ↥L) (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
        (n • finZZ p K ζ hζ hζK T hT M L hKL A hA a b hb b₀ hb₀) := by
    intro n
    induction n with
    | zero => rw [zero_smul, zero_smul, iota_zero]
    | succ n ih => simp only [add_nsmul, one_nsmul, iota_add, ih]
  have hptor_iota : p • iota (k := k) (L := ↥L) (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
        (finZZ p K ζ hζ hζK T hT M L hKL A hA a b hb b₀ hb₀) = 0 := by
    rw [hiota_nsmul, hptor, iota_zero]
  rw [← hχ L hKL L' hKL' hLL (iota (k := k) (L := ↥L)
        (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
        (finZZ p K ζ hζ hζK T hT M L hKL A hA a b hb b₀ hb₀)) hptor_iota]
  refine congrArg (fun v : extH (classesK k ↥L') 2 => χ L' hKL' v) ?_
  rw [inflLevel_def]
  rw [hz']
  rw [show iota (k := k) (L := ↥L') (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
        (extHMap (decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
            (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw')
          (finMU (K := K) A hA hLL)
          (finZZ p K ζ hζ hζK T hT M L hKL A hA a b hb b₀ hb₀))
      = extToClasses (k := k) (K := ↥L')
          (iotaLift (k := k) (L := ↥L') (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
            (extHMap (decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
              (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw')
              (finMU (K := K) A hA hLL)
              (finZZ p K ζ hζ hζK T hT M L hKL A hA a b hb b₀ hb₀))) from rfl]
  rw [iotaLift_idleRepMap k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
        (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw'
        (finMU (K := K) A hA hLL) (finMU_spec (K := K) A hA hLL)
        (finZZ p K ζ hζ hζK T hT M L hKL A hA a b hb b₀ hb₀)]
  rw [extToClasses_idleRepMap k (↥L) (↥L')
        (iotaLift (k := k) (L := ↥L) (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
          (finZZ p K ζ hζ hζK T hT M L hKL A hA a b hb b₀ hb₀))]
  rfl

/-- **The value of the finite-place half at a finite place `A`.**  The level `L ≥ K` and the
factorisation `b| = b₀ ∘ res_L` come from `Classical.choose` of
`PT.exists_level_factors_locConstOnTwo` applied at the decomposition group `H = decomp k A`; the
value is then `finAtLevel` at that level.  The two guards (`H = decomp k A`, and `b` a cocycle
there) are exactly what the local dictionary needs; off them the definition returns `0` (the guard
holds whenever `fin` is applied at the decomposition group of a finite place, which is the only
case the clauses use). -/
noncomputable def finAtValue
    (χ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
        K ≤ L → extH (classesK k L) 2 → ZMod p)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (H : Subgroup (Ω ≃ₐ[k] Ω))
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (ha : SSGRoute.IsLocConstOn H a) (hb : SSGRoute.IsLocConstOn H b) : ZMod p := by
  classical
  by_cases hH : H = SSGRoute.decomp k A
  · subst hH
    by_cases hbc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b
    · -- ## the joint finite Galois level `L` for `b|_H` (`a` is not needed: only `βl a` is used)
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
      -- the factorisation `b| = b₀ ∘ res_L` produced by the level choice
      have hb₀ : ∀ σ ∈ SSGRoute.decomp k A,
          b σ = hL.choose_spec.choose_spec.choose_spec.2.choose
            (AlgEquiv.restrictNormalHom L σ) :=
        hL.choose_spec.choose_spec.choose_spec.2.choose_spec
      -- ## the value at that level
      exact finAtLevel (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK)
        (T := T) (hT := hT) χ M A hA L hKL a b hbc
        (hL.choose_spec.choose_spec.choose_spec.2.choose) hb₀
    · exact 0
  · exact 0

end FinHalf

end Work.SSGRoute.PT
