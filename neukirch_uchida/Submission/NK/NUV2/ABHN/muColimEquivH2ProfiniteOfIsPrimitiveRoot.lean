import Mathlib
import Submission.NK.HassePrinciple.MuColimit
import Submission.NK.BrauerTwist.Profinite
import Submission.NK.BrauerHasse.Profinite
import Submission.NK.IndecomposedDeep.twistTwoComparison
import Submission.NK.NUV2.LC.muColimEquiv_h2Profinite

/-!
# `MuColim p ⊤` and `H2Profinite p ⊤` are equivalent when `K ∋ ζ_p`

Let `K` be a field containing a primitive `p`-th root of unity `ζ_p` (`p` prime) and `K'` a
separable closure of `K`.  At every finite Galois level `L/K` the cyclotomic coefficient module
`μ_p(L)` is then the *trivial* `ℤ/p`-module: every `p`-th root of unity of `L` is a power of the
image of `ζ_p`, and every `K`-algebra automorphism of `L` fixes that image.  Identifying
`μ_p(L)` with the trivial module `ℤ/p = NK.BrauerHasse.Coeff p` through the primitive root, the
level cohomologies `NK.HassePrinciple.MuLevelH2 p ⊤ L = H²(LevelGroup ⊤ L, μ_p(L))` and
`NK.BrauerHasse.LevelH2 p ⊤ L = H²(LevelGroup ⊤ L, ℤ/p)` are isomorphic, naturally in the
transition maps; collating over the finite Galois levels gives an equivalence of the two colimits
`NK.HassePrinciple.MuColim p ⊤` and `NK.BrauerHasse.H2Profinite p ⊤`.

This is the general-`p` version of `NK.NUV2.LC.muColimEquiv_h2Profinite` (the case `p = 2`, where
`μ_2 = {±1}` is trivial in characteristic `0`), and its construction follows that file line by line:
the coefficient identification `muAddEquiv` (`ruIso` followed by a fixed identification of `μ_p(K')`
with `ℤ/p` through a primitive root), its naturality for the coefficient inclusions
(`muAddEquiv_muLevelInclLinearMap`), its equivariance for the (trivial) actions
(`muAddEquiv_equivariance`), the levelwise comparison `levelCompareRoot` built from
`NK.IndecomposedDeep.H2congrEquiv` with its naturality `levelCompare_muLevelMap` from
`NK.IndecomposedDeep.H2congr_map`, and finally the two comparison maps `muToH2`/`h2ToMu` on the
colimits, built from the universal properties `NK.BrauerTwist.LevelSystem.lift` and
`NK.BrauerHasse.H2Profinite.lift`.
-/

open CategoryTheory Representation

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

universe u

namespace NK.NUV2.ABHN

section Setup

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- Every `K`-algebra automorphism of a field `F` containing `K` fixes every `p`-th root of unity,
provided `K` itself contains a primitive `p`-th root of unity. -/
theorem rootsOfUnity_smul_eq_self {F : Type u} [Field F] [Algebra K F] {p : ℕ} [NeZero p]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (σ : F ≃ₐ[K] F) (x : ↥(rootsOfUnity p F)) :
    σ • x = x := by
  have hζ' : IsPrimitiveRoot (algebraMap K F ζ) p :=
    hζ.map_of_injective (algebraMap K F).injective
  have hx : ((x : Fˣ) : F) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity p (x : Fˣ)).mp x.2, Units.val_one]
  obtain ⟨i, -, hpow⟩ := hζ'.eq_pow_of_pow_eq_one hx
  apply Subtype.ext
  rw [NK.HassePrinciple.coe_smul_rootsOfUnity]
  apply Units.ext
  rw [AlgEquiv.smul_units_def, Units.coe_map]
  rw [← hpow]
  change (σ : F ≃ₐ[K] F) ((algebraMap K F ζ) ^ i) = (algebraMap K F ζ) ^ i
  rw [map_pow, AlgEquiv.commutes]

/-- The level representation `μ_p(L)`, with its universes pinned. -/
noncomputable abbrev muLevelRepP (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    Rep.{u,u,u} NK.HassePrinciple.CoeffInt (NK.BrauerHasse.LevelGroup V L) :=
  NK.HassePrinciple.muLevelRep p V L

/-- The level representation `μ_p(L)` is trivial when `K ∋ ζ_p`. -/
lemma muLevelRep_rho_eq_self (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (g : NK.BrauerHasse.LevelGroup V L) (y : Additive ↥(rootsOfUnity p ↥L)) :
    (muLevelRepP p V L).ρ g y = y := by
  show (NK.HassePrinciple.levelGroupRestrictHom V L g) • y = y
  refine Additive.toMul.injective ?_
  rw [show Additive.toMul ((NK.HassePrinciple.levelGroupRestrictHom V L g) • y)
      = (NK.HassePrinciple.levelGroupRestrictHom V L g) • Additive.toMul y from rfl]
  exact rootsOfUnity_smul_eq_self hζ _ _

/-- The canonical identification `μ_p(L) ≃* μ_p(K')`. -/
noncomputable def ruIso (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (L : FiniteGaloisIntermediateField K K') :
    ↥(rootsOfUnity p ↥L) ≃* ↥(rootsOfUnity p K') :=
  (Subgroup.equivMapOfInjective (rootsOfUnity p ↥L) (Units.map (algebraMap ↥L K'))
    (Units.map_injective (algebraMap ↥L K').injective)).trans
  (MulEquiv.subgroupCongr
    (IsPrimitiveRoot.map_rootsOfUnity (hζ.map_of_injective (algebraMap K ↥L).injective)
      (algebraMap ↥L K').injective))

lemma ruIso_coe (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (L : FiniteGaloisIntermediateField K K') (y : ↥(rootsOfUnity p ↥L)) :
    (((ruIso p hζ L y : ↥(rootsOfUnity p K')) : (K')ˣ) : K') = ((y : (↥L)ˣ) : K') := by
  rw [ruIso, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    Subgroup.coe_equivMapOfInjective_apply, Units.coe_map]
  rfl

lemma ruIso_muLevelIncl (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') (y : ↥(rootsOfUnity p ↥L)) :
    ruIso p hζ L' (NK.HassePrinciple.muLevelIncl p L L' h y) = ruIso p hζ L y := by
  apply Subtype.ext
  apply Units.ext
  rw [ruIso_coe, ruIso_coe]
  rfl

/-- A fixed identification `Z/p ≃+ μ_p(K')`, through a primitive `p`-th root of unity of `K'`. -/
noncomputable def ruAddEquiv {p : ℕ} [NeZero p] (ζ : K') (hζ : IsPrimitiveRoot ζ p) :
    ULift.{u,0} (ZMod p) ≃+ Additive ↥(rootsOfUnity p K') :=
  (AddEquiv.ulift).trans
    ((IsPrimitiveRoot.zmodEquivZPowers (IsPrimitiveRoot.isUnit_unit (NeZero.out (n := p)) hζ)).trans
      (MulEquiv.toAdditive (MulEquiv.subgroupCongr
        (IsPrimitiveRoot.zpowers_eq (IsPrimitiveRoot.isUnit_unit (NeZero.out (n := p)) hζ)))))

/-- **The coefficient identification `μ_p(L) ≃+ Z/p`.** -/
noncomputable def muAddEquiv (p : ℕ) [NeZero p] (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (L : FiniteGaloisIntermediateField K K') :
    Additive ↥(rootsOfUnity p ↥L) ≃+ NK.BrauerHasse.Coeff.{u} p :=
  (MulEquiv.toAdditive (ruIso p hζ L)).trans
    ((ruAddEquiv (algebraMap K K' ζ)
      (hζ.map_of_injective (algebraMap K K').injective)).symm)

/-- The coefficient inclusion `μ_p(L) → μ_p(L')`, with its universes pinned. -/
noncomputable abbrev muLevelInclLinearMapP {p : ℕ} {L L' : FiniteGaloisIntermediateField K K'}
    (h : L ≤ L') :
    Additive ↥(rootsOfUnity p ↥L) →ₗ[NK.HassePrinciple.CoeffInt.{u}]
      Additive ↥(rootsOfUnity p ↥L') :=
  NK.HassePrinciple.muLevelInclLinearMap p L L' h

/-- **Naturality of the coefficient identification for the coefficient inclusions.** -/
lemma muAddEquiv_muLevelInclLinearMap (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (x : Additive ↥(rootsOfUnity p ↥L)) :
    muAddEquiv p ζ hζ L' (muLevelInclLinearMapP h x) = muAddEquiv p ζ hζ L x := by
  have hnat := ruIso_muLevelIncl p hζ h (Additive.toMul x)
  have h2 : muAddEquiv p ζ hζ L' (muLevelInclLinearMapP h x)
      = (ruAddEquiv (algebraMap K K' ζ)
          (hζ.map_of_injective (algebraMap K K').injective)).symm
          (Additive.ofMul (ruIso p hζ L'
            (NK.HassePrinciple.muLevelIncl p L L' h (Additive.toMul x)))) := rfl
  rw [h2, hnat]
  rfl

/-- The trivial level representation `Z/p` of the level group. -/
noncomputable def trivLevelRep (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    Rep.{u,u,u} (NK.BrauerHasse.Coeff.{u} p) (NK.BrauerHasse.LevelGroup V L) :=
  Rep.trivial (NK.BrauerHasse.Coeff.{u} p) (NK.BrauerHasse.LevelGroup V L)
    (NK.BrauerHasse.Coeff.{u} p)

/-- **The coefficient identification is equivariant for the (trivial) actions.** -/
theorem muAddEquiv_equivariance (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    ∀ (g : NK.BrauerHasse.LevelGroup V L) (y : Additive ↥(rootsOfUnity p ↥L)),
      muAddEquiv p ζ hζ L ((muLevelRepP p V L).ρ g y) =
        (trivLevelRep p V L).ρ g (muAddEquiv p ζ hζ L y) := by
  intro g y
  show muAddEquiv p ζ hζ L ((muLevelRepP p V L).ρ g y) =
    muAddEquiv p ζ hζ L y
  rw [muLevelRep_rho_eq_self p hζ V L g y]

/-- **The levelwise comparison** of the `μ_p`-cohomology and the trivial-coefficient cohomology. -/
noncomputable def levelCompareRoot (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    NK.HassePrinciple.MuLevelH2 p V L ≃
      NK.BrauerHasse.H2 p (NK.BrauerHasse.LevelGroup V L) :=
  NK.IndecomposedDeep.H2congrEquiv (A := muLevelRepP p V L)
    (B := trivLevelRep p V L) (muAddEquiv p ζ hζ L) (muAddEquiv_equivariance p hζ V L)

/-- **Naturality of the levelwise comparison for the transition maps.** -/
lemma levelCompare_muLevelMap (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) {L L' : FiniteGaloisIntermediateField K K'}
    (h : L ≤ L') (a : NK.HassePrinciple.MuLevelH2 p V L) :
    levelCompareRoot p hζ V L' (NK.HassePrinciple.muLevelMap p V h a) =
      NK.BrauerHasse.levelMap p (U := V) h (levelCompareRoot p hζ V L a) := by
  show NK.IndecomposedDeep.H2congr (muAddEquiv p ζ hζ L')
        (muAddEquiv_equivariance p hζ V L')
        (groupCohomology.map (NK.BrauerHasse.levelQuotHom (U := V) h)
          (NK.HassePrinciple.muLevelMapCoeff p V h) 2 a) =
      (groupCohomology.map (NK.BrauerHasse.levelQuotHom (U := V) h)
        (NK.BrauerHasse.trivHom (NK.BrauerHasse.levelQuotHom (U := V) h)) 2)
        (NK.IndecomposedDeep.H2congr (muAddEquiv p ζ hζ L)
          (muAddEquiv_equivariance p hζ V L) a)
  exact NK.IndecomposedDeep.H2congr_map (NK.BrauerHasse.levelQuotHom (U := V) h)
    (NK.HassePrinciple.muLevelMapCoeff p V h)
    (NK.BrauerHasse.trivHom (NK.BrauerHasse.levelQuotHom (U := V) h))
    (muAddEquiv p ζ hζ L) (muAddEquiv p ζ hζ L')
    (muAddEquiv_equivariance p hζ V L) (muAddEquiv_equivariance p hζ V L')
    (fun x => by
      change (muAddEquiv p ζ hζ L') (muLevelInclLinearMapP h x) =
        (muAddEquiv p ζ hζ L) x
      exact muAddEquiv_muLevelInclLinearMap p hζ h x) a

/-! ## The comparison of the colimits -/

section Colim

variable (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

/-- The comparison map from the `μ_p`-colimit to the trivial-coefficient profinite cohomology. -/
noncomputable def muToH2 :
    NK.HassePrinciple.MuColim (K := K) (K' := K') p ⊤ →
      NK.BrauerHasse.H2Profinite (K := K) (K' := K') p ⊤ :=
  (NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p ⊤).lift
    (fun L a => NK.BrauerHasse.H2Profinite.ofLevel L (levelCompareRoot p hζ ⊤ L a))
    (by
      intro L L' h a
      show NK.BrauerHasse.H2Profinite.ofLevel L'
          (levelCompareRoot p hζ ⊤ L' (NK.HassePrinciple.muLevelMap p ⊤ h a)) = _
      rw [levelCompare_muLevelMap p hζ ⊤ h a, NK.BrauerHasse.H2Profinite.ofLevel_levelMap])

/-- The comparison map from the trivial-coefficient profinite cohomology to the `μ_p`-colimit. -/
noncomputable def h2ToMu :
    NK.BrauerHasse.H2Profinite (K := K) (K' := K') p ⊤ →
      NK.HassePrinciple.MuColim (K := K) (K' := K') p ⊤ :=
  NK.BrauerHasse.H2Profinite.lift (p := p) (U := ⊤)
    (fun L b => NK.HassePrinciple.MuColim.ofLevel p ⊤ L ((levelCompareRoot p hζ ⊤ L).symm b))
    (by
      intro L L' h b
      have key : (levelCompareRoot p hζ ⊤ L').symm (NK.BrauerHasse.levelMap p (U := ⊤) h b) =
          NK.HassePrinciple.muLevelMap p ⊤ h ((levelCompareRoot p hζ ⊤ L).symm b) := by
        have h1 := levelCompare_muLevelMap p hζ ⊤ h ((levelCompareRoot p hζ ⊤ L).symm b)
        rw [Equiv.apply_symm_apply] at h1
        exact ((levelCompareRoot p hζ ⊤ L').symm_apply_eq).mpr h1.symm
      rw [key]
      exact NK.BrauerTwist.LevelSystem.ofLevel_map
        (S := NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p ⊤) h
        ((levelCompareRoot p hζ ⊤ L).symm b))

/-- The computation rule for `muToH2` on the class of a level. -/
lemma muToH2_ofLevel (L : FiniteGaloisIntermediateField K K')
    (a : (NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p ⊤).obj L) :
    muToH2 p hζ ((NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p ⊤).ofLevel L a) =
      NK.BrauerHasse.H2Profinite.ofLevel L (levelCompareRoot p hζ ⊤ L a) := rfl

/-- The computation rule for `h2ToMu` on the class of a level. -/
lemma h2ToMu_ofLevel (L : FiniteGaloisIntermediateField K K')
    (b : NK.BrauerHasse.LevelH2 p ⊤ L) :
    h2ToMu p hζ (NK.BrauerHasse.H2Profinite.ofLevel L b) =
      (NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p ⊤).ofLevel L
        ((levelCompareRoot p hζ ⊤ L).symm b) := rfl

/-- The two comparison maps are inverse on the levels. -/
lemma h2ToMu_muToH2_ofLevel (L : FiniteGaloisIntermediateField K K')
    (a : (NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p ⊤).obj L) :
    h2ToMu p hζ (muToH2 p hζ
        ((NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p ⊤).ofLevel L a)) =
      (NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p ⊤).ofLevel L a :=
  (congrArg (h2ToMu p hζ) (muToH2_ofLevel p hζ L a)).trans
    ((h2ToMu_ofLevel p hζ L (levelCompareRoot p hζ ⊤ L a)).trans
      (congrArg ((NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p ⊤).ofLevel L)
        (Equiv.symm_apply_apply (levelCompareRoot p hζ ⊤ L) a)))

/-- The two comparison maps are inverse on the levels (other direction). -/
lemma muToH2_h2ToMu_ofLevel (L : FiniteGaloisIntermediateField K K')
    (b : NK.BrauerHasse.LevelH2 p ⊤ L) :
    muToH2 p hζ (h2ToMu p hζ (NK.BrauerHasse.H2Profinite.ofLevel L b)) =
      NK.BrauerHasse.H2Profinite.ofLevel L b :=
  (congrArg (muToH2 p hζ) (h2ToMu_ofLevel p hζ L b)).trans
    ((muToH2_ofLevel p hζ L ((levelCompareRoot p hζ ⊤ L).symm b)).trans
      (congrArg (NK.BrauerHasse.H2Profinite.ofLevel L)
        (Equiv.apply_symm_apply (levelCompareRoot p hζ ⊤ L) b)))

lemma muToH2_left_inv : Function.LeftInverse (h2ToMu (K := K) (K' := K') p hζ)
    (muToH2 (K := K) (K' := K') p hζ) := by
  intro x
  obtain ⟨L, a, rfl⟩ :=
    NK.BrauerTwist.LevelSystem.ofLevel_surjective
      (S := NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p ⊤) x
  exact h2ToMu_muToH2_ofLevel p hζ L a

lemma muToH2_right_inv : Function.RightInverse (h2ToMu (K := K) (K' := K') p hζ)
    (muToH2 (K := K) (K' := K') p hζ) := by
  intro y
  obtain ⟨L, b, rfl⟩ := NK.BrauerHasse.H2Profinite.ofLevel_surjective (p := p) (U := ⊤) y
  exact muToH2_h2ToMu_ofLevel p hζ L b

/-- **The two colimits are equivalent.** -/
noncomputable def muColimEquiv :
    NK.HassePrinciple.MuColim (K := K) (K' := K') p ⊤ ≃
      NK.BrauerHasse.H2Profinite (K := K) (K' := K') p ⊤ where
  toFun := muToH2 p hζ
  invFun := h2ToMu p hζ
  left_inv := muToH2_left_inv p hζ
  right_inv := muToH2_right_inv p hζ

end Colim

end Setup

/-- **The `μ_p`-colimit and the trivial-coefficient profinite cohomology agree when `K ∋ ζ_p`.**  Let `K` be a field containing a primitive `p`-th root of unity (`p` prime) and `K'` a separable closure of `K`.  At every finite Galois level `L/K` the cyclotomic coefficient module `μ_p(L)` is then the trivial `ℤ/p`-module and is identified with `ℤ/p = NK.BrauerHasse.Coeff p` (via the primitive root), naturally in `L`; consequently the two filtered systems `NK.HassePrinciple.MuColim p ⊤ = colim_L H²(LevelGroup ⊤ L, μ_p(L))` and `NK.BrauerHasse.H2Profinite p ⊤ = colim_L H²(LevelGroup ⊤ L, ℤ/p)` have the same levels and the same transition maps, hence equivalent colimits.  This is the general-`p` version of `NK.NUV2.LC.muColimEquiv_h2Profinite` (the case `p = 2`, where `μ_2 = {±1}` is trivial in characteristic `0`); that file is a complete template for the construction: `muTwoAddEquiv` ↦ an additive equivalence `μ_p(L) ≃+ ℤ/p` built from the primitive root, `muTwoAddEquiv_equivariance` from the triviality of the action, `levelCompareRoot`/`levelCompare_muLevelMap` from `NK.IndecomposedDeep.H2congrEquiv`/`H2congr_map`, and the two comparison maps on the colimits from the universal properties `NK.BrauerTwist.LevelSystem.lift` and `NK.BrauerHasse.H2Profinite.lift`. -/
theorem muColimEquivH2ProfiniteOfIsPrimitiveRoot {K : Type u} [Field K] {K' : Type u} [Field K']
    [Algebra K K'] [IsSepClosure K K'] {p : ℕ} (hp : p.Prime)
    (hζ : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    Nonempty (NK.HassePrinciple.MuColim (K := K) (K' := K') p ⊤ ≃
      NK.BrauerHasse.H2Profinite (K := K) (K' := K') p ⊤) := by
  haveI : NeZero p := NeZero.of_pos hp.pos
  obtain ⟨ζ, hζ⟩ := hζ
  exact ⟨muColimEquiv (K := K) (K' := K') p hζ⟩

end NK.NUV2.ABHN
