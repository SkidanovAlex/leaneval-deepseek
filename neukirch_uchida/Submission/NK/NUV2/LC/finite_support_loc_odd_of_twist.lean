import Mathlib
import Submission.NK.BrauerHasse.All
import Submission.NK.BrauerTwist.All
import Submission.NK.IndecomposedDeep.twistTwoComparison
import Submission.NK.HasseTwist.Restrict
import Submission.NK.LocalDecomposition.All
import Submission.NK.HassePrinciple.H2_map_injective_of_coprime_index
import Submission.NK.NUV2.LC.finite_support_loc

/-!
# `finite_support_loc_odd_of_twist`

A class of the trivial-coefficient profinite cohomology `H²(U, Z/p)` for an **odd** prime `p` has
finite support, granted the `μ_p`-twisted finite-support statement `FiniteSupportTwist p`
(`Submission/Work/NUV2/LC/finite_support_loc.lean`).

The proof restricts to the subgroup `V = U ⊓ fixingMu p` of `U` acting trivially on `μ_p` (of index
dividing `p - 1`, hence prime to `p`) — so that at every level containing `μ_p` the trivial
coefficients `Z/p` and the cyclotomic coefficients `μ_p` agree *equivariantly* — and compares the
resulting "shadow" class of the twisted theory with the original one by a level computation.  The
helper lemmas live in the namespace `NK.NUV2.LC.OddTwist`; the deliverable is
`NK.NUV2.LC.finite_support_loc_odd_of_twist` below.
-/

open CategoryTheory Representation

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

universe u

namespace NK.NUV2.LC.OddTwist


variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## 1. The level module is everything when `μ_p ⊆ L` -/

theorem muLevel_eq_top_of_forall_mem (p : ℕ) {L : FiniteGaloisIntermediateField K K'}
    (hL : ∀ x : rootsOfUnity p K', ((x : (K')ˣ) : K') ∈ (L : IntermediateField K K')) :
    NK.BrauerTwist.muLevel p L = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  rw [NK.BrauerTwist.mem_muLevel]
  intro σ
  rw [Subgroup.smul_def]
  apply Subtype.ext
  show (↑σ : Gal(K'/K)) • ((x : (K')ˣ)) = ((x : (K')ˣ))
  rw [AlgEquiv.smul_units_def]
  apply Units.ext
  rw [Units.coe_map]
  have hx : (((x : rootsOfUnity p K') : (K')ˣ) : K') ∈ (L : IntermediateField K K') := hL x
  exact (IntermediateField.mem_fixingSubgroup_iff (L : IntermediateField K K') (↑σ)).mp σ.2 _ hx

/-! ## 2. The level representation is trivial for a subgroup fixing `μ_p` -/

theorem levelRep_rho_eq_of_fixing_mu (p : ℕ) (V : Subgroup Gal(K'/K))
    (hV : ∀ σ : Gal(K'/K), σ ∈ V → ∀ x : rootsOfUnity p K', σ • x = x)
    (L : FiniteGaloisIntermediateField K K')
    (g : NK.BrauerHasse.LevelGroup V L)
    (y : Additive ↥(NK.BrauerTwist.muLevel p L)) :
    (NK.BrauerTwist.levelRep p V L).ρ g y = y := by
  induction g using QuotientGroup.induction_on with
  | H u =>
    rw [NK.BrauerTwist.levelRep_ρ_apply]
    apply Additive.toMul.injective
    rw [show Additive.toMul ((u : Gal(K'/K)) • y) = (u : Gal(K'/K)) • Additive.toMul y from rfl]
    apply Subtype.ext
    change (u : Gal(K'/K)) • (((Additive.toMul y : ↥(NK.BrauerTwist.muLevel p L)) : rootsOfUnity p K')) =
      (((Additive.toMul y : ↥(NK.BrauerTwist.muLevel p L)) : rootsOfUnity p K'))
    exact hV (u : Gal(K'/K)) u.2 ((Additive.toMul y : ↥(NK.BrauerTwist.muLevel p L)) : rootsOfUnity p K')

/-! ## 3. The coefficient identification -/

noncomputable abbrev levelRepP (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    Rep.{u,u,u} NK.BrauerTwist.CoeffInt (NK.BrauerHasse.LevelGroup V L) :=
  NK.BrauerTwist.levelRep p V L

noncomputable abbrev trivLevelRepP (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    Rep.{u,u,u} (NK.BrauerHasse.Coeff.{u} p) (NK.BrauerHasse.LevelGroup V L) :=
  Rep.trivial (NK.BrauerHasse.Coeff.{u} p) (NK.BrauerHasse.LevelGroup V L)
    (NK.BrauerHasse.Coeff.{u} p)

noncomputable def muAddEquivRoots (p : ℕ) [NeZero p] (ζ : K') (hζ : IsPrimitiveRoot ζ p) :
    Additive ↥(rootsOfUnity p K') ≃+ NK.BrauerHasse.Coeff.{u} p :=
  ((AddEquiv.ulift (α := ZMod p)).trans
    ((IsPrimitiveRoot.zmodEquivZPowers (IsPrimitiveRoot.isUnit_unit (NeZero.out (n := p)) hζ)).trans
      (MulEquiv.toAdditive (MulEquiv.subgroupCongr
        (IsPrimitiveRoot.zpowers_eq (IsPrimitiveRoot.isUnit_unit (NeZero.out (n := p)) hζ)))))).symm

noncomputable def muAddEquivTop (p : ℕ) [NeZero p] (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (L : FiniteGaloisIntermediateField K K') (hL : NK.BrauerTwist.muLevel p L = ⊤) :
    Additive ↥(NK.BrauerTwist.muLevel p L) ≃+ NK.BrauerHasse.Coeff.{u} p :=
  (MulEquiv.toAdditive ((MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv)).trans
    (muAddEquivRoots p ζ hζ)

lemma muAddEquivTop_muIncl (p : ℕ) [NeZero p] (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (hL : NK.BrauerTwist.muLevel p L = ⊤) (hL' : NK.BrauerTwist.muLevel p L' = ⊤)
    (x : Additive ↥(NK.BrauerTwist.muLevel p L)) :
    muAddEquivTop p ζ hζ L' hL' (NK.BrauerTwist.muInclAddHom h x) =
      muAddEquivTop p ζ hζ L hL x := by
  have key : ((MulEquiv.toAdditive ((MulEquiv.subgroupCongr hL').trans Subgroup.topEquiv))
        (NK.BrauerTwist.muInclAddHom h x))
      = (MulEquiv.toAdditive ((MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv)) x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl
  show (muAddEquivRoots p ζ hζ)
      ((MulEquiv.toAdditive ((MulEquiv.subgroupCongr hL').trans Subgroup.topEquiv))
        (NK.BrauerTwist.muInclAddHom h x)) =
    (muAddEquivRoots p ζ hζ)
      ((MulEquiv.toAdditive ((MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv)) x)
  rw [key]

lemma muAddEquivTop_equivariance (p : ℕ) [NeZero p] (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K))
    (hV : ∀ σ : Gal(K'/K), σ ∈ V → ∀ x : rootsOfUnity p K', σ • x = x)
    (L : FiniteGaloisIntermediateField K K') (hL : NK.BrauerTwist.muLevel p L = ⊤) :
    ∀ (g : NK.BrauerHasse.LevelGroup V L) (y : Additive ↥(NK.BrauerTwist.muLevel p L)),
      muAddEquivTop p ζ hζ L hL ((levelRepP p V L).ρ g y) =
        (trivLevelRepP p V L).ρ g (muAddEquivTop p ζ hζ L hL y) := by
  intro g y
  show muAddEquivTop p ζ hζ L hL ((levelRepP p V L).ρ g y) = muAddEquivTop p ζ hζ L hL y
  rw [levelRep_rho_eq_of_fixing_mu p V hV L g y]

/-! ## 4. The level comparison -/

noncomputable def levelCompareOfTop (p : ℕ) [NeZero p] (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K))
    (hV : ∀ σ : Gal(K'/K), σ ∈ V → ∀ x : rootsOfUnity p K', σ • x = x) :
    ∀ (L : FiniteGaloisIntermediateField K K') (hL : NK.BrauerTwist.muLevel p L = ⊤),
      NK.BrauerTwist.LevelH2 p V L ≃ NK.BrauerHasse.LevelH2 p V L :=
  fun L hL => NK.IndecomposedDeep.H2congrEquiv (A := levelRepP p V L)
    (B := trivLevelRepP p V L) (muAddEquivTop p ζ hζ L hL)
    (muAddEquivTop_equivariance p ζ hζ V hV L hL)

lemma levelCompareOfTop_levelMap (p : ℕ) [NeZero p] (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K))
    (hV : ∀ σ : Gal(K'/K), σ ∈ V → ∀ x : rootsOfUnity p K', σ • x = x)
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (hL : NK.BrauerTwist.muLevel p L = ⊤) (hL' : NK.BrauerTwist.muLevel p L' = ⊤)
    (a : NK.BrauerTwist.LevelH2 p V L) :
    levelCompareOfTop p ζ hζ V hV L' hL' (NK.BrauerTwist.levelMap p V h a) =
      NK.BrauerHasse.levelMap p (U := V) h (levelCompareOfTop p ζ hζ V hV L hL a) := by
  show NK.IndecomposedDeep.H2congr (muAddEquivTop p ζ hζ L' hL')
        (muAddEquivTop_equivariance p ζ hζ V hV L' hL')
        (groupCohomology.map (NK.BrauerHasse.levelQuotHom (U := V) h)
          (NK.BrauerTwist.levelMapCoeff p V h) 2 a) =
      (groupCohomology.map (NK.BrauerHasse.levelQuotHom (U := V) h)
        (NK.BrauerHasse.trivHom (NK.BrauerHasse.levelQuotHom (U := V) h)) 2)
        (NK.IndecomposedDeep.H2congr (muAddEquivTop p ζ hζ L hL)
          (muAddEquivTop_equivariance p ζ hζ V hV L hL) a)
  exact NK.IndecomposedDeep.H2congr_map (NK.BrauerHasse.levelQuotHom (U := V) h)
    (NK.BrauerTwist.levelMapCoeff p V h)
    (NK.BrauerHasse.trivHom (NK.BrauerHasse.levelQuotHom (U := V) h))
    (muAddEquivTop p ζ hζ L hL) (muAddEquivTop p ζ hζ L' hL')
    (muAddEquivTop_equivariance p ζ hζ V hV L hL)
    (muAddEquivTop_equivariance p ζ hζ V hV L' hL')
    (fun x => by
      change (muAddEquivTop p ζ hζ L' hL') (NK.BrauerTwist.muInclAddHom h x) =
        (muAddEquivTop p ζ hζ L hL) x
      exact muAddEquivTop_muIncl p ζ hζ h hL hL' x) a

lemma levelCompareOfTop_levelRes (p : ℕ) [NeZero p] (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    {U V : Subgroup Gal(K'/K)} (hVU : V ≤ U)
    (hU : ∀ σ : Gal(K'/K), σ ∈ U → ∀ x : rootsOfUnity p K', σ • x = x)
    (hV : ∀ σ : Gal(K'/K), σ ∈ V → ∀ x : rootsOfUnity p K', σ • x = x)
    (L : FiniteGaloisIntermediateField K K') (hL : NK.BrauerTwist.muLevel p L = ⊤)
    (a : NK.BrauerTwist.LevelH2 p U L) :
    levelCompareOfTop p ζ hζ V hV L hL (NK.HasseTwist.levelRes p hVU L a) =
      NK.BrauerHasse.H2.map (NK.BrauerHasse.levelInclHom hVU L)
        (levelCompareOfTop p ζ hζ U hU L hL a) := by
  show NK.IndecomposedDeep.H2congr (muAddEquivTop p ζ hζ L hL)
        (muAddEquivTop_equivariance p ζ hζ V hV L hL)
        (groupCohomology.map (NK.BrauerHasse.levelInclHom hVU L)
          (NK.HasseTwist.levelResCoeff p hVU L) 2 a) =
      (groupCohomology.map (NK.BrauerHasse.levelInclHom hVU L)
        (NK.BrauerHasse.trivHom (NK.BrauerHasse.levelInclHom hVU L)) 2)
        (NK.IndecomposedDeep.H2congr (muAddEquivTop p ζ hζ L hL)
          (muAddEquivTop_equivariance p ζ hζ U hU L hL) a)
  exact NK.IndecomposedDeep.H2congr_map (NK.BrauerHasse.levelInclHom hVU L)
    (NK.HasseTwist.levelResCoeff p hVU L)
    (NK.BrauerHasse.trivHom (NK.BrauerHasse.levelInclHom hVU L))
    (muAddEquivTop p ζ hζ L hL) (muAddEquivTop p ζ hζ L hL)
    (muAddEquivTop_equivariance p ζ hζ U hU L hL)
    (muAddEquivTop_equivariance p ζ hζ V hV L hL)
    (fun x => by
      change (muAddEquivTop p ζ hζ L hL) (NK.BrauerTwist.muInclAddHom (le_refl L) x) =
        (muAddEquivTop p ζ hζ L hL) x
      exact muAddEquivTop_muIncl p ζ hζ (le_refl L) hL hL x) a



open NK.BrauerHasse

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## 5. The cofinal comparison of the colimits -/

section Part3

variable (p : ℕ) [NeZero p]

/-- **The twisted localisation at a place is the restriction to the decomposition group.** -/
theorem H2Twist_loc_eq_res (U : Subgroup Gal(K'/K)) (A : NK.BrauerTwist.OverFinitePrime K K')
    (x : NK.BrauerTwist.H2Twist p U) :
    NK.BrauerTwist.H2Twist.loc p U x A =
      NK.HasseTwist.H2Twist.res p
        (inf_le_left : U ⊓ NK.BrauerTwist.stabSubgroup A.1 ≤ U) x := by
  obtain ⟨L, a, rfl⟩ := NK.BrauerTwist.H2Twist.ofLevel_surjective p U x
  rw [NK.BrauerTwist.H2Twist.loc_ofLevel_apply, NK.HasseTwist.H2Twist.res_ofLevel]
  rfl

/-- **Killing criterion for the trivial coefficients**: a level class vanishes in the colimit iff
it is killed by inflation to a larger level. -/
lemma H2Profinite_ofLevel_eq_zero_iff {U : Subgroup Gal(K'/K)}
    {L : FiniteGaloisIntermediateField K K'} (a : NK.BrauerHasse.LevelH2 p U L) :
    NK.BrauerHasse.H2Profinite.ofLevel L a = 0 ↔
      ∃ (M : FiniteGaloisIntermediateField K K') (h : L ≤ M),
        NK.BrauerHasse.levelMap p (U := U) h a = 0 := by
  constructor
  · intro h0
    obtain ⟨M, h1, h2, heq⟩ :=
      (NK.BrauerHasse.ofLevel_eq_iff (U := U) a (0 : NK.BrauerHasse.LevelH2 p U ⊥)).mp h0
    refine ⟨M, h1, ?_⟩
    rw [map_zero] at heq
    exact heq
  · rintro ⟨M, h, hz⟩
    rw [← NK.BrauerHasse.H2Profinite.ofLevel_levelMap (p := p) (U := U) h a, hz]
    exact NK.BrauerHasse.ofLevel_zero M

/-- **Killing criterion for the twisted coefficients**. -/
lemma H2Twist_ofLevel_eq_zero_iff {U : Subgroup Gal(K'/K)}
    {L : FiniteGaloisIntermediateField K K'} (a : NK.BrauerTwist.LevelH2 p U L) :
    NK.BrauerTwist.H2Twist.ofLevel p U L a = 0 ↔
      ∃ (M : FiniteGaloisIntermediateField K K') (h : L ≤ M),
        NK.BrauerTwist.levelMap p U h a = 0 := by
  constructor
  · intro h0
    obtain ⟨M, h1, h2, heq⟩ :=
      (NK.BrauerTwist.H2Twist.ofLevel_eq_iff p U a
        (0 : NK.BrauerTwist.LevelH2 p U ⊥)).mp h0
    refine ⟨M, h1, ?_⟩
    rw [map_zero] at heq
    exact heq
  · rintro ⟨M, h, hz⟩
    rw [← NK.BrauerTwist.H2Twist.ofLevel_levelMap p U h a, hz]
    exact NK.HasseTwist.H2Twist.ofLevel_zero (p := p) M

/-- The level square for the inflation and the restriction, trivial coefficients. -/
lemma levelMap_triv_levelInclHom_apply {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    {L M : FiniteGaloisIntermediateField K K'} (h : L ≤ M) (a : NK.BrauerHasse.LevelH2 p U L) :
    NK.BrauerHasse.levelMap p (U := V) h
        ((NK.BrauerHasse.H2.map (NK.BrauerHasse.levelInclHom hV L)).hom a) =
      (NK.BrauerHasse.H2.map (NK.BrauerHasse.levelInclHom hV M)).hom
        (NK.BrauerHasse.levelMap p (U := U) h a) := by
  rw [NK.BrauerHasse.levelMap, NK.BrauerHasse.levelMap]
  rw [← CategoryTheory.comp_apply, ← NK.BrauerHasse.H2.map_comp,
    NK.HasseTwist.levelQuotHom_levelInclHom_comp (U := U) (V := V) hV h,
    NK.BrauerHasse.H2.map_comp]
  rfl

/-- Composition in the trivial level system. -/
lemma levelMap_triv_comp_apply {U : Subgroup Gal(K'/K)}
    {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'} (h₁ : L₁ ≤ L₂) (h₂ : L₂ ≤ L₃)
    (a : NK.BrauerHasse.LevelH2 p U L₁) :
    NK.BrauerHasse.levelMap p (U := U) h₂ (NK.BrauerHasse.levelMap p (U := U) h₁ a) =
      NK.BrauerHasse.levelMap p (U := U) (h₁.trans h₂) a := by
  have h := congrArg
    (fun (k : NK.BrauerHasse.LevelH2 p U L₁ ⟶ NK.BrauerHasse.LevelH2 p U L₃) => k.hom a)
    (NK.BrauerHasse.levelMap_comp (p := p) (U := U) h₁ h₂)
  simpa [ModuleCat.comp_apply] using h

/-- Composition in the twisted level system. -/
lemma levelMap_twist_comp_apply {U : Subgroup Gal(K'/K)}
    {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'} (h₁ : L₁ ≤ L₂) (h₂ : L₂ ≤ L₃)
    (a : NK.BrauerTwist.LevelH2 p U L₁) :
    NK.BrauerTwist.levelMap p U h₂ (NK.BrauerTwist.levelMap p U h₁ a) =
      NK.BrauerTwist.levelMap p U (h₁.trans h₂) a := by
  have h := congrArg
    (fun (k : NK.BrauerTwist.LevelH2 p U L₁ ⟶ NK.BrauerTwist.LevelH2 p U L₃) => k.hom a)
    (NK.BrauerTwist.levelMap_comp (p := p) (U := U) h₁ h₂)
  simpa [ModuleCat.comp_apply] using h

end Part3


section Part3b

/-- Monotonicity of the "the level module is everything" hypothesis. -/
lemma muLevel_eq_top_of_mono (p : ℕ) {M N : FiniteGaloisIntermediateField K K'}
    (hM : NK.BrauerTwist.muLevel p M = ⊤) (h : M ≤ N) :
    NK.BrauerTwist.muLevel p N = ⊤ := by
  rw [Subgroup.eq_top_iff'] at hM ⊢
  intro x
  exact NK.BrauerTwist.muLevel_mono h (hM x)

lemma muLevel_eq_top_of_le (p : ℕ) (L₀ : FiniteGaloisIntermediateField K K')
    (hL₀ : ∀ x : rootsOfUnity p K', ((x : (K')ˣ) : K') ∈ (L₀ : IntermediateField K K'))
    {M : FiniteGaloisIntermediateField K K'} (h : L₀ ≤ M) :
    NK.BrauerTwist.muLevel p M = ⊤ :=
  muLevel_eq_top_of_forall_mem p (L := M)
    (fun x => (FiniteGaloisIntermediateField.le_iff L₀ M).mp h (hL₀ x))

lemma levelCompareOfTop_zero (p : ℕ) [NeZero p] (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K))
    (hV : ∀ σ : Gal(K'/K), σ ∈ V → ∀ x : rootsOfUnity p K', σ • x = x)
    (L : FiniteGaloisIntermediateField K K') (hL : NK.BrauerTwist.muLevel p L = ⊤) :
    levelCompareOfTop p ζ hζ V hV L hL 0 = 0 :=
  NK.IndecomposedDeep.H2congr_zero (A := levelRepP p V L) (B := trivLevelRepP p V L)
    (muAddEquivTop p ζ hζ L hL) (muAddEquivTop_equivariance p ζ hζ V hV L hL)

lemma levelCompareOfTop_inv_levelMap (p : ℕ) [NeZero p] (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K))
    (hV : ∀ σ : Gal(K'/K), σ ∈ V → ∀ x : rootsOfUnity p K', σ • x = x)
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (hL : NK.BrauerTwist.muLevel p L = ⊤) (hL' : NK.BrauerTwist.muLevel p L' = ⊤)
    (w : NK.BrauerHasse.LevelH2 p V L) :
    NK.BrauerTwist.levelMap p V h
        ((levelCompareOfTop p ζ hζ V hV L hL).symm w) =
      (levelCompareOfTop p ζ hζ V hV L' hL').symm
        (NK.BrauerHasse.levelMap p (U := V) h w) := by
  have h1 := levelCompareOfTop_levelMap p ζ hζ V hV h hL hL'
    ((levelCompareOfTop p ζ hζ V hV L hL).symm w)
  rw [Equiv.apply_symm_apply] at h1
  exact (((levelCompareOfTop p ζ hζ V hV L' hL').symm_apply_eq).mpr h1.symm).symm

/-- The inverse form of `levelCompareOfTop_levelRes`. -/
lemma levelRes_inv_levelCompareOfTop (p : ℕ) [NeZero p] (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    {U V : Subgroup Gal(K'/K)} (hVU : V ≤ U)
    (hU : ∀ σ : Gal(K'/K), σ ∈ U → ∀ x : rootsOfUnity p K', σ • x = x)
    (hV : ∀ σ : Gal(K'/K), σ ∈ V → ∀ x : rootsOfUnity p K', σ • x = x)
    (L : FiniteGaloisIntermediateField K K') (hL : NK.BrauerTwist.muLevel p L = ⊤)
    (x : NK.BrauerHasse.LevelH2 p U L) :
    NK.HasseTwist.levelRes p hVU L ((levelCompareOfTop p ζ hζ U hU L hL).symm x) =
      (levelCompareOfTop p ζ hζ V hV L hL).symm
        (NK.BrauerHasse.H2.map (NK.BrauerHasse.levelInclHom hVU L) x) := by
  have h1 := levelCompareOfTop_levelRes p ζ hζ hVU hU hV L hL
    ((levelCompareOfTop p ζ hζ U hU L hL).symm x)
  rw [Equiv.apply_symm_apply] at h1
  exact ((((levelCompareOfTop p ζ hζ V hV L hL).symm_apply_eq).mpr h1.symm)).symm

/-- **The `μ_p`-shadow of a level class**: the class of the twisted theory obtained from the
level class `a` of the trivial theory by inflating to a level `M ≥ L` containing `μ_p` and
applying the level comparison. -/
noncomputable def twistedShadow (p : ℕ) [NeZero p] (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K))
    (hV : ∀ σ : Gal(K'/K), σ ∈ V → ∀ x : rootsOfUnity p K', σ • x = x)
    {L M : FiniteGaloisIntermediateField K K'} (hM : NK.BrauerTwist.muLevel p M = ⊤)
    (hLM : L ≤ M) (a : NK.BrauerHasse.LevelH2 p V L) :
    NK.BrauerTwist.H2Twist p V :=
  NK.BrauerTwist.H2Twist.ofLevel p V M
    ((levelCompareOfTop p ζ hζ V hV M hM).symm
      (NK.BrauerHasse.levelMap p (U := V) hLM a))

/-- **The localisation of the shadow controls the localisation of the class.** -/
theorem loc_twist_shadow_ne_zero (p : ℕ) [NeZero p] (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K))
    (hV : ∀ σ : Gal(K'/K), σ ∈ V → ∀ x : rootsOfUnity p K', σ • x = x)
    {L M : FiniteGaloisIntermediateField K K'} (hM : NK.BrauerTwist.muLevel p M = ⊤)
    (hLM : L ≤ M) (a : NK.BrauerHasse.LevelH2 p V L)
    (A : NK.BrauerHasse.OverFinitePrime K K')
    (h : NK.BrauerHasse.H2Profinite.loc p V (NK.BrauerHasse.H2Profinite.ofLevel L a) A ≠ 0) :
    NK.BrauerTwist.H2Twist.loc p V (twistedShadow p ζ hζ V hV hM hLM a) A ≠ 0 := by
  intro hy
  apply h
  rw [NK.LocalDecomposition.loc_eq_res p V A (NK.BrauerHasse.H2Profinite.ofLevel L a)]
  -- the level class of the shadow
  set yM : NK.BrauerTwist.LevelH2 p V M :=
    (levelCompareOfTop p ζ hζ V hV M hM).symm
      (NK.BrauerHasse.levelMap p (U := V) hLM a) with hyM
  have hshadow : twistedShadow p ζ hζ V hV hM hLM a =
      NK.BrauerTwist.H2Twist.ofLevel p V M yM := rfl
  -- the twisted restriction vanishes
  have hy' : NK.HasseTwist.H2Twist.res p
      (inf_le_left : V ⊓ NK.BrauerTwist.stabSubgroup A.1 ≤ V)
      (NK.BrauerTwist.H2Twist.ofLevel p V M yM) = 0 := by
    rw [← hshadow, ← H2Twist_loc_eq_res p V A (twistedShadow p ζ hζ V hV hM hLM a)]
    exact hy
  rw [NK.HasseTwist.H2Twist.res_ofLevel] at hy'
  obtain ⟨N, hMN, hNz⟩ :=
    (H2Twist_ofLevel_eq_zero_iff p (U := V ⊓ NK.BrauerTwist.stabSubgroup A.1) _).mp hy'
  -- abbreviations
  set G : Subgroup Gal(K'/K) := V ⊓ NK.BrauerTwist.stabSubgroup A.1 with hG
  have hV' : ∀ σ : Gal(K'/K), σ ∈ G → ∀ x : rootsOfUnity p K', σ • x = x :=
    fun σ hσ => hV σ hσ.1
  have hGn : NK.BrauerTwist.muLevel p N = ⊤ := muLevel_eq_top_of_mono p hM hMN
  -- move the inflation inside the restriction
  rw [← NK.HasseTwist.levelRes_levelMap_apply p (inf_le_left :
    V ⊓ NK.BrauerTwist.stabSubgroup A.1 ≤ V) hMN yM] at hNz
  -- push the inflation through the comparison
  rw [levelCompareOfTop_inv_levelMap p ζ hζ V hV hMN hM hGn
    (NK.BrauerHasse.levelMap p (U := V) hLM a)] at hNz
  -- push the restriction through the comparison
  rw [levelRes_inv_levelCompareOfTop p ζ hζ (inf_le_left :
      V ⊓ NK.BrauerTwist.stabSubgroup A.1 ≤ V) hV hV' N hGn
      (NK.BrauerHasse.levelMap p (U := V) hMN (NK.BrauerHasse.levelMap p (U := V) hLM a))]
    at hNz
  -- the comparison is an equivalence, so the inner class vanishes
  have hW : NK.BrauerHasse.H2.map (NK.BrauerHasse.levelInclHom (inf_le_left :
        V ⊓ NK.BrauerTwist.stabSubgroup A.1 ≤ V) N)
      (NK.BrauerHasse.levelMap p (U := V) hMN
        (NK.BrauerHasse.levelMap p (U := V) hLM a)) = 0 := by
    have hthis := congrArg (levelCompareOfTop p ζ hζ G hV' N hGn) hNz
    rw [Equiv.apply_symm_apply, levelCompareOfTop_zero p ζ hζ G hV' N hGn] at hthis
    exact hthis
  -- conclude on the trivial side
  rw [NK.LocalDecomposition.H2Profinite.res_ofLevel]
  refine (H2Profinite_ofLevel_eq_zero_iff p (U := G) _).mpr ⟨N, hLM.trans hMN, ?_⟩
  rw [levelMap_triv_levelInclHom_apply p (U := V) (V := G) (inf_le_left :
    V ⊓ NK.BrauerTwist.stabSubgroup A.1 ≤ V) (hLM.trans hMN) a]
  rw [← levelMap_triv_comp_apply p (U := V) hLM hMN a]
  exact hW

end Part3b


variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The subgroup acting trivially on `μ_p` -/

noncomputable def fixingMu (p : ℕ) : Subgroup Gal(K'/K) :=
  (MulDistribMulAction.toMulAut Gal(K'/K) ↥(rootsOfUnity p K')).ker

lemma mem_fixingMu_iff (p : ℕ) (σ : Gal(K'/K)) :
    σ ∈ fixingMu (K := K) (K' := K') p ↔ ∀ x : rootsOfUnity p K', σ • x = x := by
  rw [fixingMu, MonoidHom.mem_ker, MulEquiv.ext_iff]
  constructor
  · intro h x
    simpa [MulDistribMulAction.toMulAut_apply] using h x
  · intro h x
    simpa [MulDistribMulAction.toMulAut_apply] using h x

theorem index_subgroupOf_fixingMu_coprime (p : ℕ) (hp : p.Prime) (U : Subgroup Gal(K'/K))
    (hζ : ∃ ζ : K', IsPrimitiveRoot ζ p) :
    Nat.Coprime (Subgroup.index ((fixingMu (K := K) (K' := K') p).subgroupOf U)) p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hζ
  have hcard : Nat.card ↥(rootsOfUnity p K') = p := hζ.card_rootsOfUnity
  haveI hfin : Finite ↥(rootsOfUnity p K') :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have hmult : Nat.card (MulAut ↥(rootsOfUnity p K')) = p - 1 := by
    rw [IsCyclic.card_mulAut, hcard, Nat.totient_prime hp]
  set φ : Gal(K'/K) →* MulAut ↥(rootsOfUnity p K') :=
    MulDistribMulAction.toMulAut Gal(K'/K) ↥(rootsOfUnity p K') with hφ
  have hker : φ.ker.subgroupOf U = (φ.comp U.subtype).ker := rfl
  have hidx : Subgroup.index (φ.ker.subgroupOf U) = Nat.card ↥(φ.comp U.subtype).range := by
    rw [hker, Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (φ.comp U.subtype)).toEquiv
  have hle : Nat.card ↥(φ.comp U.subtype).range ≤ p - 1 := by
    calc Nat.card ↥(φ.comp U.subtype).range
        ≤ Nat.card (MulAut ↥(rootsOfUnity p K')) :=
          Nat.card_le_card_of_injective
            (fun x : ↥(φ.comp U.subtype).range => (x : MulAut ↥(rootsOfUnity p K')))
            Subtype.coe_injective
      _ = p - 1 := hmult
  have hpos : 0 < Nat.card ↥(φ.comp U.subtype).range := Nat.card_pos
  change Nat.Coprime (Subgroup.index (φ.ker.subgroupOf U)) p
  rw [hidx, Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hdvd
  have := Nat.le_of_dvd hpos hdvd
  omega

/-! ## The index of the range of a level inclusion -/

lemma levelInclHom_comp (p : ℕ) {W U V : Subgroup Gal(K'/K)} (hVU : V ≤ U) (hUW : U ≤ W)
    (L : FiniteGaloisIntermediateField K K') :
    (NK.BrauerHasse.levelInclHom (U := W) (V := U) hUW L).comp
        (NK.BrauerHasse.levelInclHom (U := U) (V := V) hVU L) =
      NK.BrauerHasse.levelInclHom (U := W) (V := V) (hVU.trans hUW) L := by
  apply MonoidHom.ext
  intro z
  induction z using QuotientGroup.induction_on with
  | H v =>
    simp only [MonoidHom.comp_apply, NK.BrauerHasse.levelInclHom, QuotientGroup.map_mk]
    exact congrArg (QuotientGroup.mk' (L.fixingSubgroup.subgroupOf W)) (Subtype.ext rfl)

lemma range_levelInclHom_eq (p : ℕ) {U V : Subgroup Gal(K'/K)} (hVU : V ≤ U)
    (M : FiniteGaloisIntermediateField K K') :
    MonoidHom.range (NK.BrauerHasse.levelInclHom hVU M) =
      (V.subgroupOf U).map (QuotientGroup.mk' (M.fixingSubgroup.subgroupOf U)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    induction x using QuotientGroup.induction_on with
    | H v =>
      refine Subgroup.mem_map.mpr ⟨Subgroup.inclusion hVU v, v.2, ?_⟩
      simp only [QuotientGroup.mk'_apply, NK.BrauerHasse.levelInclHom, QuotientGroup.map_mk]
  · intro hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    refine MonoidHom.mem_range.mpr ⟨QuotientGroup.mk' (M.fixingSubgroup.subgroupOf V) ⟨u, hu⟩, ?_⟩
    simp only [QuotientGroup.mk'_apply, NK.BrauerHasse.levelInclHom, QuotientGroup.map_mk]
    exact congrArg (QuotientGroup.mk' (M.fixingSubgroup.subgroupOf U)) (Subtype.ext rfl)

lemma index_range_levelInclHom_dvd (p : ℕ) {U V : Subgroup Gal(K'/K)} (hVU : V ≤ U)
    (M : FiniteGaloisIntermediateField K K') :
    Subgroup.index (MonoidHom.range (NK.BrauerHasse.levelInclHom hVU M)) ∣
      Subgroup.index (V.subgroupOf U) := by
  rw [range_levelInclHom_eq p hVU M, Subgroup.index_map]
  rw [QuotientGroup.ker_mk', QuotientGroup.range_mk', Subgroup.index_top, mul_one]
  exact Subgroup.index_dvd_of_le (le_sup_left : V.subgroupOf U ≤ V.subgroupOf U ⊔
    (M.fixingSubgroup.subgroupOf U))

lemma coprime_index_range_levelInclHom (p : ℕ) (hp : p.Prime) {U V : Subgroup Gal(K'/K)}
    (hVU : V ≤ U) (hfix : U ⊓ fixingMu (K := K) (K' := K') p ≤ V)
    (hζ : ∃ ζ : K', IsPrimitiveRoot ζ p) (M : FiniteGaloisIntermediateField K K') :
    Nat.Coprime (Subgroup.index (MonoidHom.range (NK.BrauerHasse.levelInclHom hVU M))) p := by
  have hfix' : (fixingMu (K := K) (K' := K') p).subgroupOf U ≤ V.subgroupOf U := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_subgroupOf]
    exact hfix ⟨x.2, hx⟩
  exact Nat.Coprime.coprime_dvd_left
    ((index_range_levelInclHom_dvd p hVU M).trans (Subgroup.index_dvd_of_le hfix'))
    (index_subgroupOf_fixingMu_coprime p hp U hζ)

/-! ## Restriction on `H²(·, Z/p)` is injective for a subgroup containing the fixing subgroup -/

theorem H2Profinite_res_comp (p : ℕ) {W U V : Subgroup Gal(K'/K)}
    (hVU : V ≤ U) (hUW : U ≤ W) (x : H2Profinite p W) :
    NK.LocalDecomposition.H2Profinite.res p hVU
        (NK.LocalDecomposition.H2Profinite.res p hUW x) =
      NK.LocalDecomposition.H2Profinite.res p (hVU.trans hUW) x := by
  obtain ⟨L, a, rfl⟩ := H2Profinite.ofLevel_surjective x
  rw [NK.LocalDecomposition.H2Profinite.res_ofLevel,
    NK.LocalDecomposition.H2Profinite.res_ofLevel,
    NK.LocalDecomposition.H2Profinite.res_ofLevel]
  congr 1
  have hcomp : NK.BrauerHasse.H2.map (p := p)
        (NK.BrauerHasse.levelInclHom (U := W) (V := U) hUW L) ≫
      NK.BrauerHasse.H2.map (p := p) (NK.BrauerHasse.levelInclHom (U := U) (V := V) hVU L) =
      NK.BrauerHasse.H2.map (p := p) (NK.BrauerHasse.levelInclHom (U := W) (V := V)
        (hVU.trans hUW) L) := by
    rw [← NK.BrauerHasse.H2.map_comp]
    congr 1
    exact levelInclHom_comp p hVU hUW L
  have h2 := congrArg (fun (k : NK.BrauerHasse.LevelH2 p W L ⟶ NK.BrauerHasse.LevelH2 p V L) =>
    k.hom a) hcomp
  simpa [ModuleCat.comp_apply] using h2

theorem H2Profinite_res_injective_of_le (p : ℕ) (hp : p.Prime) {V U : Subgroup Gal(K'/K)}
    (hVU : V ≤ U) (hfix : U ⊓ fixingMu (K := K) (K' := K') p ≤ V)
    (hζ : ∃ ζ : K', IsPrimitiveRoot ζ p) :
    Function.Injective (NK.LocalDecomposition.H2Profinite.res p hVU) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro x y hxy
  obtain ⟨L, a, rfl⟩ := H2Profinite.ofLevel_surjective x
  obtain ⟨L', b, rfl⟩ := H2Profinite.ofLevel_surjective y
  rw [NK.LocalDecomposition.H2Profinite.res_ofLevel,
    NK.LocalDecomposition.H2Profinite.res_ofLevel] at hxy
  obtain ⟨M, h₁, h₂, heq⟩ := (NK.BrauerHasse.ofLevel_eq_iff _ _).mp hxy
  rw [levelMap_triv_levelInclHom_apply p hVU h₁ a,
    levelMap_triv_levelInclHom_apply p hVU h₂ b] at heq
  have hinj := NK.HassePrinciple.H2_map_injective_of_coprime_index (p := p)
    (NK.BrauerHasse.levelInclHom (U := U) (V := V) hVU M)
    (NK.HassePrinciple.levelInclHom_injective hVU M)
    (coprime_index_range_levelInclHom p hp hVU hfix hζ M)
  have h : NK.BrauerHasse.levelMap p (U := U) h₁ a =
      NK.BrauerHasse.levelMap p (U := U) h₂ b := hinj heq
  exact (NK.BrauerHasse.ofLevel_eq_iff a b).mpr ⟨M, h₁, h₂, h⟩

lemma H2Profinite_res_zero (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U) :
    NK.LocalDecomposition.H2Profinite.res p h (0 : H2Profinite p U) = 0 := by
  show NK.LocalDecomposition.H2Profinite.res p h
    (H2Profinite.ofLevel (⊥ : FiniteGaloisIntermediateField K K')
      (0 : NK.BrauerHasse.LevelH2 p U ⊥)) = 0
  rw [NK.LocalDecomposition.H2Profinite.res_ofLevel, map_zero]
  exact NK.BrauerHasse.ofLevel_zero ⊥

theorem H2Profinite_loc_res_ne_zero (p : ℕ) (hp : p.Prime) {V U : Subgroup Gal(K'/K)}
    (hVU : V ≤ U) (hfix : U ⊓ fixingMu (K := K) (K' := K') p ≤ V)
    (hζ : ∃ ζ : K', IsPrimitiveRoot ζ p) (A : OverFinitePrime K K') (x : H2Profinite p U)
    (hx : NK.BrauerHasse.H2Profinite.loc p U x A ≠ 0) :
    NK.BrauerHasse.H2Profinite.loc p V
      (NK.LocalDecomposition.H2Profinite.res p hVU x) A ≠ 0 := by
  intro h0
  apply hx
  -- the local decomposition groups
  set D : Subgroup Gal(K'/K) := stabSubgroup A.1 with hD
  have hG : V ⊓ D ≤ U ⊓ D := fun z hz => ⟨hVU hz.1, hz.2⟩
  have hfixG : (U ⊓ D) ⊓ fixingMu (K := K) (K' := K') p ≤ V ⊓ D := by
    intro z hz
    exact ⟨hfix ⟨hz.1.1, hz.2⟩, hz.1.2⟩
  have hinj := H2Profinite_res_injective_of_le (K := K) (K' := K') p hp hG hfixG hζ
  -- rewrite both localisations as restrictions
  rw [NK.LocalDecomposition.loc_eq_res p U A x]
  have h0' : NK.LocalDecomposition.H2Profinite.res p (inf_le_left : V ⊓ D ≤ V)
      (NK.LocalDecomposition.H2Profinite.res p hVU x) = 0 := by
    rw [← NK.LocalDecomposition.loc_eq_res p V A
      (NK.LocalDecomposition.H2Profinite.res p hVU x)]
    exact h0
  -- combine the two restrictions
  have hcomb : NK.LocalDecomposition.H2Profinite.res p (inf_le_left : V ⊓ D ≤ V)
      (NK.LocalDecomposition.H2Profinite.res p hVU x) =
      NK.LocalDecomposition.H2Profinite.res p
        (show V ⊓ D ≤ U from fun z hz => hVU hz.1) x := by
    rw [H2Profinite_res_comp p (inf_le_left : V ⊓ D ≤ V) hVU x]
  rw [hcomb] at h0'
  -- conclude by injectivity
  have h0'' : NK.LocalDecomposition.H2Profinite.res p hG
      (NK.LocalDecomposition.H2Profinite.res p (inf_le_left : U ⊓ D ≤ U) x) = 0 := by
    rw [H2Profinite_res_comp p hG (inf_le_left : U ⊓ D ≤ U) x]
    exact h0'
  apply hinj
  exact h0''.trans (H2Profinite_res_zero p hG).symm

/-! ## A primitive `p`-th root of unity and a level containing `μ_p` -/

theorem exists_isPrimitiveRoot_of_isSepClosure {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (hp : p.Prime) [NeZero (p : K')] :
    ∃ ζ : K', IsPrimitiveRoot ζ p := by
  have hsep : IsSepClosed K' := IsSepClosure.sep_closed K
  have hdeg : (Polynomial.cyclotomic p K').degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic, Nat.totient_prime hp]
    exact_mod_cast Nat.sub_ne_zero_of_lt hp.one_lt
  obtain ⟨z, hz⟩ := IsSepClosed.exists_root (Polynomial.cyclotomic p K') hdeg
    (Polynomial.separable_cyclotomic p K')
  exact ⟨z, Polynomial.isRoot_cyclotomic_iff.mp hz⟩

noncomputable def chosenPrimitiveRoot {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (hp : p.Prime) [NeZero (p : K')] : K' :=
  Classical.choose (exists_isPrimitiveRoot_of_isSepClosure (K := K) (K' := K') p hp)

lemma chosenPrimitiveRoot_spec {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (hp : p.Prime) [NeZero (p : K')] :
    IsPrimitiveRoot (chosenPrimitiveRoot (K := K) (K' := K') p hp) p :=
  Classical.choose_spec (exists_isPrimitiveRoot_of_isSepClosure (K := K) (K' := K') p hp)

noncomputable def levelContainingMu {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (hp : p.Prime) [NeZero (p : K')] :
    FiniteGaloisIntermediateField K K' :=
  FiniteGaloisIntermediateField.adjoin K
    ({(chosenPrimitiveRoot (K := K) (K' := K') p hp)} : Set K')

lemma levelContainingMu_spec {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (hp : p.Prime) [NeZero (p : K')] :
    ∀ x : rootsOfUnity p K',
      ((x : (K')ˣ) : K') ∈
        (levelContainingMu (K := K) (K' := K') p hp : IntermediateField K K') := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro x
  have hζ := chosenPrimitiveRoot_spec (K := K) (K' := K') p hp
  have hx : ((x : (K')ˣ) : K') ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity p (x : (K')ˣ)).mp x.2, Units.val_one]
  obtain ⟨i, -, hpow⟩ := hζ.eq_pow_of_pow_eq_one hx
  have hxeq : (((x : (K')ˣ)) : K') = (chosenPrimitiveRoot (K := K) (K' := K') p hp) ^ i :=
    hpow.symm
  rw [hxeq]
  exact pow_mem (FiniteGaloisIntermediateField.subset_adjoin K _ (Set.mem_singleton _)) i


end NK.NUV2.LC.OddTwist

namespace NK.NUV2.LC

open NK.NUV2.LC.OddTwist

theorem finite_support_loc_odd_of_twist (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h : NK.NUV2.LC.FiniteSupportTwist p) {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K'] {U : Subgroup Gal(K'/K)} (x : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p U) : {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) | ∃ A : NK.BrauerHasse.OverFinitePrime K K', A.1.comap (algebraMap K K') = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 ∧ NK.BrauerHasse.H2Profinite.loc p U x A ≠ 0}.Finite := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p : K') := ⟨by
    intro h0
    have h1 : algebraMap K K' (p : K) = 0 := by rw [map_natCast]; exact h0
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) ((algebraMap K K').injective (by rw [h1, map_zero]))⟩
  -- a primitive `p`-th root of unity and a level containing all of `μ_p`
  set ζ : K' := chosenPrimitiveRoot (K := K) (K' := K') p hp with hζdef
  have hζ : IsPrimitiveRoot ζ p := chosenPrimitiveRoot_spec (K := K) (K' := K') p hp
  set L₀ : FiniteGaloisIntermediateField K K' :=
    levelContainingMu (K := K) (K' := K') p hp with hL₀def
  have hL₀ : ∀ y : rootsOfUnity p K',
      ((y : (K')ˣ) : K') ∈ (L₀ : IntermediateField K K') :=
    levelContainingMu_spec (K := K) (K' := K') p hp
  have hζex : ∃ ζ' : K', IsPrimitiveRoot ζ' p := ⟨ζ, hζ⟩
  -- the subgroup acting trivially on `μ_p`, and the class restricted to it
  set V : Subgroup Gal(K'/K) := U ⊓ fixingMu (K := K) (K' := K') p with hVdef
  have hVU : V ≤ U := inf_le_left
  have hfix : U ⊓ fixingMu (K := K) (K' := K') p ≤ V := le_rfl
  have hVtriv : ∀ σ : Gal(K'/K), σ ∈ V → ∀ y : rootsOfUnity p K', σ • y = y :=
    fun σ hσ => (mem_fixingMu_iff (K := K) (K' := K') p σ).mp hσ.2
  set z : NK.BrauerHasse.H2Profinite p V :=
    NK.LocalDecomposition.H2Profinite.res p hVU x with hzdef
  obtain ⟨L, a, ha⟩ := NK.BrauerHasse.H2Profinite.ofLevel_surjective z
  -- the `μ_p`-shadow of `a`
  have hμM : NK.BrauerTwist.muLevel p (L ⊔ L₀) = ⊤ :=
    muLevel_eq_top_of_le (K := K) (K' := K') p L₀ hL₀ (le_sup_right : L₀ ≤ L ⊔ L₀)
  set y : NK.BrauerTwist.H2Twist p V :=
    twistedShadow (K := K) (K' := K') p ζ hζ V hVtriv hμM (le_sup_left : L ≤ L ⊔ L₀) a
    with hydef
  refine (h y).subset ?_
  rintro 𝔭 ⟨A, hAcomap, hAloc⟩
  refine ⟨A, hAcomap, ?_⟩
  -- the localisation of the restriction does not vanish
  have hzloc : NK.BrauerHasse.H2Profinite.loc p V z A ≠ 0 := by
    rw [hzdef]
    exact H2Profinite_loc_res_ne_zero (K := K) (K' := K') p hp hVU hfix hζex A x hAloc
  -- so the twisted shadow is locally non-trivial at `A`
  have hshadow : NK.BrauerTwist.H2Twist.loc p V y A ≠ 0 := by
    rw [hydef]
    refine loc_twist_shadow_ne_zero (K := K) (K' := K') p ζ hζ V hVtriv hμM
      (le_sup_left : L ≤ L ⊔ L₀) a A ?_
    rw [ha]
    exact hzloc
  exact hshadow


end NK.NUV2.LC
