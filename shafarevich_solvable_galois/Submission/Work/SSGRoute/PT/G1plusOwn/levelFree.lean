import Mathlib
import Submission.Work.SSGRoute.PT.g1plus_finHalf
import Submission.Work.SSGRoute.PT.G1plusLevel.finAtLevel_add_right
import Submission.Work.SSGRoute.PT.pairAlgebra
import Submission.Work.SSGRoute.PT.G1plusLevelClauses
import Submission.Work.SSGRoute.PT.G1plusLevel.finAtValue_coboundary_right
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `G1⁺`: level-free clause lemmas for the finite-place half `fin`

`PT.finAtValue` (`Submission/Work/SSGRoute/PT/g1plus_finHalf.lean`) chooses its admissible level
with `Classical.choose` from `PT.exists_level_factors_locConstOn` applied to its second argument `b`
(never to `a`).  Consequently:

* clauses (1) (additivity in `a`) and (3) (vanishing on a coboundary) are *level-free* — the
  arguments `a`, `a'`, `a + a'` all unfold at the *same* chosen level, and the existing
  `PT.finAtValue_add_left` / `PT.finAtValue_coboundary_left` / `..._coboundary_right` exploit this;
* clause (2) (additivity in `b`) compares values at *different* chosen levels (`b + b'` versus `b`
  and `b'`), so it needs the level independence `PT.finAtLevel_eq_of_le`.

The bridge is `finAtValue_eq_finAtLevel`: the value at the internally chosen level equals the value
at *any* admissible level (both levels factor `b`), because any two levels are dominated by their
compositum `L₀ ⊔ L`, on which the two values agree by `PT.finAtLevel_eq_of_le` (the factorisation of
`b` at `L₀ ⊔ L` being `b₀ ∘ galRes`).

With it, clause (2) becomes `PT.finAtLevel_add_right` at a level (`exists_level_factors_locConstOnTwo`)
factoring both `b` and `b'` simultaneously.
-/

open scoped TensorProduct Pointwise
open SSGRoute.PTExt

noncomputable section

namespace Work.SSGRoute.PT.G1pOwn

set_option maxHeartbeats 20000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open Classical

/-- The `χ`-family of `G1⁺`: a coherent `p`-torsion invariant of `H²(Gal(L/k), C_L)` over the levels
`L ≤ Ω` containing `K` (the S1 object `PT.coherent_pTorsion_chi_k`). -/
abbrev ChiK (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] : Type :=
  ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
    K ≤ L → extH (classesK k L) 2 → ZMod p

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
  (χ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      K ≤ L → extH (classesK k L) 2 → ZMod p)

/-- **`finAtValue` unfolds at any admissible level.**  If `b|_H` (`H = decomp k A`) is a cocycle
and factors through `Gal(L/k)` via `b₀`, then the value of `finAtValue` equals `finAtLevel` at `L`
— even though `finAtValue` internally uses a different (`Classical.choose`d) level. -/
theorem finAtValue_eq_finAtLevel
    (hχ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
        [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
        (u : extH (classesK k L) 2),
        p • u = 0 → χ L' hKL' (inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (ha : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (hb : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hbc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L)
    (b₀ : (↥L ≃ₐ[k] ↥L) → DualMod p (M ⊗[ZMod p] T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)) :
    finAtValue p k Ω K ζ hζ hζK T hT χ M A hA (SSGRoute.decomp k A) a b ha hb
      = finAtLevel p k Ω K ζ hζ hζK T hT χ M A hA L hKL a b hbc b₀ hb₀ := by
  classical
  -- the level chosen inside `finAtValue` (it depends on `b` alone)
  have hL := exists_level_factors_locConstOn p k Ω K
    (M := DualMod p (M ⊗[ZMod p] T)) (SSGRoute.decomp k A) b hb
  let L₀ := hL.choose
  have hL₀fin : FiniteDimensional k L₀ := hL.choose_spec.choose
  have hL₀norm : Normal k L₀ := hL.choose_spec.choose_spec.choose
  have hKL₀ : K ≤ L₀ := hL.choose_spec.choose_spec.choose_spec.1
  have hb₀₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ =
      hL.choose_spec.choose_spec.choose_spec.2.choose (AlgEquiv.restrictNormalHom L₀ σ) :=
    hL.choose_spec.choose_spec.choose_spec.2.choose_spec
  -- the unfolding of `finAtValue`
  have hval : finAtValue p k Ω K ζ hζ hζK T hT χ M A hA (SSGRoute.decomp k A) a b ha hb
      = finAtLevel p k Ω K ζ hζ hζK T hT χ M A hA L₀ hKL₀ a b hbc
          (hL.choose_spec.choose_spec.choose_spec.2.choose) hb₀₀ := by
    simp only [finAtValue]
    rw [dif_pos trivial, dif_pos hbc]
  rw [hval]
  -- a common upper bound of the two levels
  letI : FiniteDimensional k L₀ := hL₀fin
  letI : Normal k L₀ := hL₀norm
  letI : IsGalois k L₀ := inferInstance
  letI : NumberField L₀ := inferInstance
  letI : Algebra ↥L ↥(L₀ ⊔ L) := (IntermediateField.inclusion le_sup_right).toAlgebra
  haveI : IsScalarTower k ↥L ↥(L₀ ⊔ L) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥L ↥(L₀ ⊔ L) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra ↥L₀ ↥(L₀ ⊔ L) := (IntermediateField.inclusion le_sup_left).toAlgebra
  haveI : IsScalarTower k ↥L₀ ↥(L₀ ⊔ L) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥L₀ ↥(L₀ ⊔ L) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- the factorisation of `b` at the compositum, obtained from the one at `L`
  let b₀'' : (↥(L₀ ⊔ L) ≃ₐ[k] ↥(L₀ ⊔ L)) → DualMod p (M ⊗[ZMod p] T) :=
    fun τ => b₀ (galRes k ↥L ↥(L₀ ⊔ L) τ)
  have hb₀'' : ∀ σ ∈ SSGRoute.decomp k A,
      b σ = b₀'' (AlgEquiv.restrictNormalHom ↥(L₀ ⊔ L) σ) := by
    intro σ hσ
    rw [hb₀ σ hσ]
    refine congrArg b₀ ?_
    exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply (K₁ := ↥L) (K₂ := ↥(L₀ ⊔ L))
      (F := k) (K₃ := Ω) σ)
  -- two applications of level independence, both landing at `L₀ ⊔ L`
  have e1 : finAtLevel p k Ω K ζ hζ hζK T hT χ M A hA L₀ hKL₀ a b hbc
        (hL.choose_spec.choose_spec.choose_spec.2.choose) hb₀₀
      = finAtLevel p k Ω K ζ hζ hζK T hT χ M A hA (L₀ ⊔ L) (hKL₀.trans le_sup_left) a b hbc
          b₀'' hb₀'' :=
    finAtLevel_eq_of_le p k Ω K ζ hζ hζK T hT χ hχ M A hA a b hbc L₀ (L₀ ⊔ L)
      hKL₀ (hKL₀.trans le_sup_left) le_sup_left
      (hL.choose_spec.choose_spec.choose_spec.2.choose) b₀'' hb₀₀ hb₀''
  have e2 : finAtLevel p k Ω K ζ hζ hζK T hT χ M A hA L hKL a b hbc b₀ hb₀
      = finAtLevel p k Ω K ζ hζ hζK T hT χ M A hA (L₀ ⊔ L) (hKL.trans le_sup_right) a b hbc
          b₀'' hb₀'' :=
    finAtLevel_eq_of_le p k Ω K ζ hζ hζK T hT χ hχ M A hA a b hbc L (L₀ ⊔ L)
      hKL (hKL.trans le_sup_right) le_sup_right b₀ b₀'' hb₀ hb₀''
  rw [e1, e2]

/-- **Clause (2) of `G1⁺`'s finite half, level-free**: additivity in the second variable.

Level-free *because* of `finAtValue_eq_finAtLevel`: both `b` and `b'` factor at the common level
produced by `PT.exists_level_factors_locConstOnTwo`, at which `finAtValue` may be unfolded, and
`PT.G1plusLevel.finAtLevel_add_right` applies there. -/
theorem finAtValue_add_right
    (hχ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
        [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
        (u : extH (classesK k L) 2),
        p • u = 0 → χ L' hKL' (inflLevel L L' hLL u) = χ L hKL u)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u v : extH (classesK k L) 2),
        p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → M) (b b' : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (ha : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (hb : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hb' : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b')
    (hbadd : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (b + b'))
    (hbc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hbc' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b') :
    finAtValue p k Ω K ζ hζ hζK T hT χ M A hA (SSGRoute.decomp k A) a (b + b') ha hbadd
      = finAtValue p k Ω K ζ hζ hζK T hT χ M A hA (SSGRoute.decomp k A) a b ha hb
        + finAtValue p k Ω K ζ hζ hζK T hT χ M A hA (SSGRoute.decomp k A) a b' ha hb' := by
  classical
  obtain ⟨L, hLfin, hLnorm, hKL, b₀, b₀', hb₀, hb₀'⟩ :=
    exists_level_factors_locConstOnTwo k Ω K (SSGRoute.decomp k A) b b' hb hb'
  letI : FiniteDimensional k L := hLfin
  letI : Normal k L := hLnorm
  letI : IsGalois k L := inferInstance
  letI : NumberField L := inferInstance
  have hbcadd : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (b + b') :=
    SSGRoute.IsCocycleOn.add hbc hbc'
  have hb₀add : ∀ σ ∈ SSGRoute.decomp k A,
      (b + b') σ = (fun τ => b₀ τ + b₀' τ) (AlgEquiv.restrictNormalHom L σ) := by
    intro σ hσ
    rw [Pi.add_apply, hb₀ σ hσ, hb₀' σ hσ]
  rw [finAtValue_eq_finAtLevel p k Ω K ζ hζ hζK T hT χ hχ M A hA a (b + b') ha hbadd hbcadd L hKL
        (fun τ => b₀ τ + b₀' τ) hb₀add,
      finAtValue_eq_finAtLevel p k Ω K ζ hζ hζK T hT χ hχ M A hA a b ha hb hbc L hKL b₀ hb₀,
      finAtValue_eq_finAtLevel p k Ω K ζ hζ hζK T hT χ hχ M A hA a b' ha hb' hbc' L hKL b₀' hb₀']
  exact G1plusLevel.finAtLevel_add_right p k Ω K ζ hζ hζK T hT χ hχadd M A hA L hKL a b b'
    hbc hbc' hbcadd b₀ b₀' hb₀ hb₀' hb₀add


/-- **The finite-place half of `G1⁺`** (`fin` in the target file): at a finite-place decomposition
group `H = decomp k A` (with witness place `A'`, the `Classical.choose` of the guard) the value is
`finAtValue` at `A'`, the *group* argument being the canonically transported `decomp k A'` — this is
what makes the clause statements unfold without any subgroup transport. -/
noncomputable def g1FinHalf (χ : ChiK p k Ω K T)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T)) : ZMod p :=
  if h : ∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧ H = SSGRoute.decomp k A then
    if hc : SSGRoute.IsLocConstOn H a ∧ SSGRoute.IsLocConstOn H b then
      finAtValue p k Ω K ζ hζ hζK T hT χ M h.choose h.choose_spec.1
        (SSGRoute.decomp k h.choose) a b (h.choose_spec.2 ▸ hc.1) (h.choose_spec.2 ▸ hc.2)
    else 0
  else 0

/-- Unfolding of `g1FinHalf` through its two guards. -/
theorem g1FinHalf_eq_of_guard (χ : ChiK p k Ω K T)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (h : ∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧ H = SSGRoute.decomp k A)
    (hc : SSGRoute.IsLocConstOn H a ∧ SSGRoute.IsLocConstOn H b) :
    g1FinHalf p k Ω K ζ hζ hζK T hT χ M H a b
      = finAtValue p k Ω K ζ hζ hζK T hT χ M h.choose h.choose_spec.1
          (SSGRoute.decomp k h.choose) a b (h.choose_spec.2 ▸ hc.1) (h.choose_spec.2 ▸ hc.2) := by
  classical
  unfold g1FinHalf
  rw [dif_pos h, dif_pos hc]

/-- `g1FinHalf` vanishes off the finite-place decomposition groups. -/
theorem g1FinHalf_eq_zero_of_not (χ : ChiK p k Ω K T)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (h : ¬ ∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧ H = SSGRoute.decomp k A) :
    g1FinHalf p k Ω K ζ hζ hζK T hT χ M H a b = 0 := by
  classical
  unfold g1FinHalf
  rw [dif_neg h]

/-- `g1FinHalf` vanishes when one argument is not locally constant. -/
theorem g1FinHalf_eq_zero_of_not_locConst (χ : ChiK p k Ω K T)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (h : ∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧ H = SSGRoute.decomp k A)
    (hc : ¬ (SSGRoute.IsLocConstOn H a ∧ SSGRoute.IsLocConstOn H b)) :
    g1FinHalf p k Ω K ζ hζ hζK T hT χ M H a b = 0 := by
  classical
  unfold g1FinHalf
  rw [dif_pos h, dif_neg hc]

/-- **Clause (1) of `G1⁺`'s finite half** at `H = decomp k A`: additivity in the first variable. -/
theorem g1FinHalf_add_left (χ : ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u v : extH (classesK k L) 2),
        p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a a' : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (ha : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (ha' : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a')
    (hb : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (haa : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (a + a'))
    (hca : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a)
    (hca' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a') :
    g1FinHalf p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) (a + a') b
      = g1FinHalf p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a b
        + g1FinHalf p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a' b := by
  classical
  let hw : ∃ A' : ValuationSubring Ω, SSGRoute.IsFinPlace k A' ∧
      SSGRoute.decomp k A = SSGRoute.decomp k A' := ⟨A, hA, rfl⟩
  have hg := g1FinHalf_eq_of_guard p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) (a + a') b
    hw ⟨haa, hb⟩
  have hg' := g1FinHalf_eq_of_guard p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a b
    hw ⟨ha, hb⟩
  have hg'' := g1FinHalf_eq_of_guard p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a' b
    hw ⟨ha', hb⟩
  rw [hg, hg', hg'']
  exact finAtValue_add_left p k Ω K ζ hζ hζK T hT χ hχadd M hw.choose hw.choose_spec.1
    a a' b (hw.choose_spec.2 ▸ ha) (hw.choose_spec.2 ▸ hb) (hw.choose_spec.2 ▸ ha')
    (hw.choose_spec.2 ▸ haa) (hw.choose_spec.2 ▸ hca) (hw.choose_spec.2 ▸ hca')

/-- **Clause (2) of `G1⁺`'s finite half** at `H = decomp k A`: additivity in the second variable. -/
theorem g1FinHalf_add_right (χ : ChiK p k Ω K T)
    (hχ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
        [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
        (u : extH (classesK k L) 2),
        p • u = 0 → χ L' hKL' (inflLevel L L' hLL u) = χ L hKL u)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u v : extH (classesK k L) 2),
        p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → M) (b b' : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (ha : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (hb : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hb' : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b')
    (hbadd : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (b + b'))
    (hcb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hcb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b') :
    g1FinHalf p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a (b + b')
      = g1FinHalf p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a b
        + g1FinHalf p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a b' := by
  classical
  let hw : ∃ A' : ValuationSubring Ω, SSGRoute.IsFinPlace k A' ∧
      SSGRoute.decomp k A = SSGRoute.decomp k A' := ⟨A, hA, rfl⟩
  have hg := g1FinHalf_eq_of_guard p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a (b + b')
    hw ⟨ha, hbadd⟩
  have hg' := g1FinHalf_eq_of_guard p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a b
    hw ⟨ha, hb⟩
  have hg'' := g1FinHalf_eq_of_guard p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a b'
    hw ⟨ha, hb'⟩
  rw [hg, hg', hg'']
  exact finAtValue_add_right p k Ω K ζ hζ hζK T hT χ hχ hχadd M hw.choose hw.choose_spec.1
    a b b' (hw.choose_spec.2 ▸ ha) (hw.choose_spec.2 ▸ hb) (hw.choose_spec.2 ▸ hb')
    (hw.choose_spec.2 ▸ hbadd) (hw.choose_spec.2 ▸ hcb) (hw.choose_spec.2 ▸ hcb')

/-- **Clause (3) of `G1⁺`'s finite half** at `H = decomp k A`: vanishing when one argument is a
coboundary. -/
theorem g1FinHalf_coboundary (χ : ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u v : extH (classesK k L) 2),
        p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (ha : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (hb : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hca : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a)
    (hcb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hcob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∨
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b) :
    g1FinHalf p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a b = 0 := by
  classical
  let hw : ∃ A' : ValuationSubring Ω, SSGRoute.IsFinPlace k A' ∧
      SSGRoute.decomp k A = SSGRoute.decomp k A' := ⟨A, hA, rfl⟩
  have hg := g1FinHalf_eq_of_guard p k Ω K ζ hζ hζK T hT χ M (SSGRoute.decomp k A) a b
    hw ⟨ha, hb⟩
  rw [hg]
  rcases hcob with hcob | hcob
  · exact finAtValue_coboundary_left p k Ω K ζ hζ hζK T hT χ hχadd M hw.choose hw.choose_spec.1
      a b (hw.choose_spec.2 ▸ ha) (hw.choose_spec.2 ▸ hb) (hw.choose_spec.2 ▸ hca)
      (hw.choose_spec.2 ▸ hcob)
  · exact G1plusLevel.finAtValue_coboundary_right p k Ω K ζ hζ hζK T hT χ hχadd M hw.choose
      hw.choose_spec.1 a b (hw.choose_spec.2 ▸ ha) (hw.choose_spec.2 ▸ hb)
      (hw.choose_spec.2 ▸ hcob)

/-- The *kernel* clause of the local dictionary: `finZB` (the `Classical.choose` of
`Work.SSGRoute.local_ext_h1_bridge`) vanishes exactly on the coboundaries. -/
theorem isCoboundaryOn_of_finZB_eq_zero
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (hca : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a)
    (hla : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (h : finZB p K ζ hζ hζK T hT M A hA a = 0) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) a := by
  exact (finZB_eq_zero_iff p k Ω K ζ hζ hζK T hT M A hA a hca hla).mp h

end Work.SSGRoute.PT.G1pOwn
