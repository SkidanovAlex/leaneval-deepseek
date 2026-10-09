/-
# Hasse's theorem for the Brauer group in the `D_A`-form: `Work.SSGRoute.HasseUnits`

The arithmetic core of the `Ш²(k,M)` development: a continuous `2`-cocycle on `G_k = k̄ ≃ₐ[k] k̄`
with values in `k̄ˣ` which is a coboundary on the decomposition group of every finite place of `k̄`
and on `⟨σ⟩` for every involution `σ` is a coboundary.

The proof is the classical one, organised through the *finite levels*:

1. `Work.SSGRoute.sha2_level.exists_level_of_locallyConstant` factors `d` through a finite Galois
   level `L/k` with values in `Lˣ`; `levelCocycle` descends `d` to a `2`-cocycle on `Gal(L/k)` with
   values in `Lˣ` (`levelCocycle_value`, `levelCocycle_isCocycle`);
2. the `D_A`- and involution-conditions show that this level class is locally trivial at every
   place of `L` (`locUnits_levelClass_eq_zero_finitePlace`,
   `locUnits_levelClass_eq_zero_infinitePlace`);
3. relative Hasse–Brauer–Noether (`NK.GlobalCFTdeep.hbnUnits`) makes the level class zero
   (`exists_levelCoboundary_of_locUnits_vanishing`);
4. the level coboundary lifts to a global one (`mem_B2_of_levelCoboundary`).
-/
import Mathlib
import Submission.Work.SSGRoute.sha2_defs
import Submission.Work.AbsoluteKummer.All
import Submission.Work.SSGRoute.sha2_level.exists_level_of_locallyConstant
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.Work.SSGRoute.sha2_hasse.Defs
import Submission.Work.SSGRoute.sha2_hasse.locUnits_levelClass_eq_zero_finitePlace
import Submission.Work.SSGRoute.sha2_hasse.locUnits_levelClass_eq_zero_infinitePlace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

noncomputable section

open scoped Classical

namespace Work.SSGRoute.sha2_hasse

open Work.AbsoluteKummer

theorem hasseUnits (k : Type) [Field k] [NumberField k] : Work.SSGRoute.HasseUnits k := by
  intro d hZ hDA hinv
  -- the cocycle condition and local constancy of the given cocycle
  have hdcoc : ∀ g h l : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      d (g * h) l + d g h = g • d h l + d g (h * l) := by
    intro g h l
    have h := (Work.GroupCohomology.mem_Z2_iff (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
      (Additive (AlgebraicClosure k)ˣ) (fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
        (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => d p.1 p.2)).mp hZ.1 g h l
    exact h
  have hlc : Work.AbsoluteKummer.IsLocallyConstant
      (fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
        (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => d p.1 p.2) := hZ.2
  -- step 1: the finite level
  obtain ⟨L, hfac, hvals0⟩ :=
    Work.SSGRoute.sha2_level.exists_level_of_locallyConstant k
      (fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
        (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => d p.1 p.2) hlc
  have hvals : ∀ g h : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      ∃ x : (Lf L)ˣ, inclUnits L (Additive.ofMul x) = d g h := by
    intro g h
    obtain ⟨x, hx⟩ := hvals0 g h
    exact ⟨x, by simpa [inclUnits_ofMul] using congrArg Additive.ofMul hx⟩
  -- step 2: the descended cocycle is a cocycle
  let A : Rep.{0, 0, 0} NK.HassePrinciple.CoeffInt (Lf L ≃ₐ[k] Lf L) := levelRepK L
  let c : (Lf L ≃ₐ[k] Lf L) × (Lf L ≃ₐ[k] Lf L) → ↑A :=
    fun p => (levelCocycle L d hvals p.1 p.2 : ↑A)
  have hmem : c ∈ groupCohomology.cocycles₂ A := by
    rw [mem_cocycles₂_iff]
    intro g h l
    show (g • levelCocycle L d hvals h l : Additive (Lf L)ˣ) - levelCocycle L d hvals (g * h) l
      + levelCocycle L d hvals g (h * l) - levelCocycle L d hvals g h = 0
    have hcl : levelCocycle L d hvals (g * h) l + levelCocycle L d hvals g h
        = g • levelCocycle L d hvals h l + levelCocycle L d hvals g (h * l) :=
      levelCocycle_isCocycle L d hvals hfac hdcoc g h l
    have h2 : (g • levelCocycle L d hvals h l : Additive (Lf L)ˣ) - levelCocycle L d hvals (g * h) l
        + levelCocycle L d hvals g (h * l) - levelCocycle L d hvals g h
        = ((g • levelCocycle L d hvals h l : Additive (Lf L)ˣ) + levelCocycle L d hvals g (h * l))
          - (levelCocycle L d hvals (g * h) l + levelCocycle L d hvals g h) := by abel
    rw [h2, ← hcl, sub_self]
  -- step 3: local triviality at every place of the level
  have hloc : ∀ w : NK.GlobalCFT.Place (Lf L),
      (NK.HassePrinciple.locUnits k (Lf L) w).hom (levelClass L d hvals hmem) = 0 := by
    intro w
    cases w with
    | inl v =>
      exact locUnits_levelClass_eq_zero_infinitePlace d L hfac hvals hinv hmem v
    | inr q =>
      exact locUnits_levelClass_eq_zero_finitePlace d L hfac hvals hDA hmem q
  -- step 4: relative Hasse–Brauer–Noether at the level
  obtain ⟨f, hf⟩ := exists_levelCoboundary_of_locUnits_vanishing L c hmem hloc
  -- step 5: the splitting step
  let f' : (Lf L ≃ₐ[k] Lf L) → Additive (Lf L)ˣ := fun γ => (f γ : Additive (Lf L)ˣ)
  have hf' : ∀ γ δ : Lf L ≃ₐ[k] Lf L,
      levelCocycle L d hvals γ δ = γ • f' δ - f' (γ * δ) + f' γ := by
    intro γ δ
    have h := hf γ δ
    rw [show A.ρ γ (f δ) = (γ • f' δ : Additive (Lf L)ˣ) from rfl] at h
    show levelCocycle L d hvals γ δ = (γ • f' δ : Additive (Lf L)ˣ) - (f' (γ * δ)) + (f' γ)
    exact h.symm
  exact mem_B2_of_levelCoboundary L d (levelCocycle L d hvals)
    (fun g h => levelCocycle_value L d hvals hfac (levelRes L g) (levelRes L h) g h rfl rfl)
    f' hf'

end Work.SSGRoute.sha2_hasse
