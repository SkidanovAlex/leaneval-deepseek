import Mathlib
import Submission.Work.RatHurewicz.SphereThomDefs
import Submission.Work.Serre.bijective_mixedCup_of_two_subset
import Submission.Work.Serre.relCohMV_les_rat

/-!
# Vanishing of the rational relative cohomology of a union of two open pieces

**Main result** (`Work.RatHurewicz.relCohUnionVanish`).  Let `A, Uc, Vc ⊆ X` with `Uc`, `Vc` open
and let `J : ℕ`.  If the rational relative cohomology `H^k(Uc, Uc ∩ A; ℚ)` vanishes for all
`k ≤ J`, and likewise for `Vc` and for `Uc ∩ Vc`, then `H^k(Uc ∪ Vc, (Uc ∪ Vc) ∩ A; ℚ)` vanishes
for `1 ≤ k ≤ J`.

The proof is the (relative) Mayer–Vietoris long exact sequence of the open cover
`(Uc ∪ Vc) = Uc ∪ Vc` of the subspace `↥(Uc ∪ Vc)`
(`Work.Serre.relCohMV_les_rat`, whose exactness statements are `Work.Serre.exact_mvF_mvG`,
`Work.Serre.exact_mvG_mvDelta`, `Work.Serre.exact_mvDelta_mvF`):  the rung

  `H^{k-1}(U∩V, U∩V∩A) --δ--> H^k(X,A) --F--> H^k(U,U∩A) ⊞ H^k(V,V∩A)`

has both neighbours vanishing in the range considered, so `F` is injective into a subsingleton
module, whence `H^k(X,A) = 0`.

The hypotheses over `Uc`, `Vc`, `Uc ∩ Vc` are read inside the subspace `↥(Uc ∪ Vc)` along the
canonical homeomorphisms `↥W ≃ₜ ↥{y : ↥(Uc ∪ Vc) | (y : X) ∈ W}`
(`Work.Serre.subsingleton_relCoh_twoSubset`).
-/

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- A biproduct of two subsingleton `ℚ`-modules is a subsingleton. -/
theorem subsingleton_biprod_rat (M N : ModuleCat ℚ) [Subsingleton ↥M] [Subsingleton ↥N] :
    Subsingleton ↥(M ⊞ N) :=
  ⟨fun a b => (ModuleCat.biprodIsoProd M N).toLinearEquiv.injective (Subsingleton.elim _ _)⟩

/-- **Mayer–Vietoris: a rational relative cohomology vanishing glues over an open cover.**

For `U, V ⊆ Z` open with `U ∪ V = Z` and `A ⊆ Z`:  if `H^k(U, U∩A;ℚ)`, `H^k(V, V∩A;ℚ)` and
`H^k(U∩V, U∩V∩A;ℚ)` all vanish for `k ≤ J`, then `H^k(Z,A;ℚ)` vanishes for `1 ≤ k ≤ J`. -/
theorem relCoh_vanish_union_of_openCover {Z : Type} [TopologicalSpace Z] (A U V : Set Z)
    (hUo : IsOpen U) (hVo : IsOpen V) (hcov : U ∪ V = Set.univ) (J : ℕ)
    (hU : ∀ k : ℕ, k ≤ J → Subsingleton ↥(Work.Serre.mvCohU (TopCat.of Z) A U k))
    (hV : ∀ k : ℕ, k ≤ J → Subsingleton ↥(Work.Serre.mvCohV (TopCat.of Z) A V k))
    (hUV : ∀ k : ℕ, k ≤ J → Subsingleton ↥(Work.Serre.mvCohUV (TopCat.of Z) A U V k)) :
    ∀ k : ℕ, 1 ≤ k → k ≤ J → Subsingleton ↥(Work.Thom.RelCoh ℚ k Z A) := by
  intro k _ hkJ
  -- replace `k` by `k' + 1`, so that `k - 1` is definitionally `k'`
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  -- the two neighbours in the Mayer–Vietoris rung vanish
  haveI hUk : Subsingleton ↥(Work.Serre.mvCohU (TopCat.of Z) A U (k' + 1)) :=
    hU (k' + 1) hkJ
  haveI hVk : Subsingleton ↥(Work.Serre.mvCohV (TopCat.of Z) A V (k' + 1)) :=
    hV (k' + 1) hkJ
  haveI hUVp : Subsingleton ↥(Work.Serre.mvCohUV (TopCat.of Z) A U V k') :=
    hUV k' (le_trans (Nat.le_succ k') hkJ)
  -- exactness at `H^{k'+1}`: `ker (mvF (k'+1)) = range (mvDelta k') = 0`
  have hex := Work.Serre.exact_mvDelta_mvF (TopCat.of Z) A U V hUo hVo hcov k'
  have hdelta : (Work.Serre.mvDelta (TopCat.of Z) A U V hUo hVo hcov k').hom = 0 :=
    LinearMap.ext fun x => by rw [Subsingleton.elim x 0]; simp
  have hker : LinearMap.ker (Work.Serre.mvF (TopCat.of Z) A U V (k' + 1)).hom = ⊥ := by
    rw [← hex, hdelta, LinearMap.range_zero]
  -- hence `mvF (k'+1)` is injective, and its target is a subsingleton
  have hinj : Function.Injective (Work.Serre.mvF (TopCat.of Z) A U V (k' + 1)).hom :=
    LinearMap.ker_eq_bot.mp hker
  haveI : Subsingleton ↥(Work.Serre.mvCohU (TopCat.of Z) A U (k' + 1) ⊞
      Work.Serre.mvCohV (TopCat.of Z) A V (k' + 1)) := subsingleton_biprod_rat _ _
  exact ⟨fun a b => hinj (Subsingleton.elim _ _)⟩

/-- **Vanishing of the rational relative cohomology of a union of two open pieces.**

If the relative cohomology `H^k(W, W ∩ A; ℚ)` vanishes for `k ≤ J` for the three pieces
`W = Uc`, `W = Vc` and `W = Uc ∩ Vc`, then it vanishes for `W = Uc ∪ Vc` in degrees `1 ≤ k ≤ J`. -/
theorem relCohUnionVanish {X : Type} [TopologicalSpace X] (A Uc Vc : Set X)
    (hUo : IsOpen Uc) (hVo : IsOpen Vc) (J : ℕ)
    (hU : ∀ k : ℕ, k ≤ J → Subsingleton ↥(Work.Thom.RelCoh ℚ k ↥Uc {y : ↥Uc | (y : X) ∈ A}))
    (hV : ∀ k : ℕ, k ≤ J → Subsingleton ↥(Work.Thom.RelCoh ℚ k ↥Vc {y : ↥Vc | (y : X) ∈ A}))
    (hUV : ∀ k : ℕ, k ≤ J → Subsingleton ↥(Work.Thom.RelCoh ℚ k ↥(Uc ∩ Vc)
      {y : ↥(Uc ∩ Vc) | (y : X) ∈ A})) :
    ∀ k : ℕ, 1 ≤ k → k ≤ J → Subsingleton ↥(Work.Thom.RelCoh ℚ k ↥(Uc ∪ Vc)
      {y : ↥(Uc ∪ Vc) | (y : X) ∈ A}) := by
  -- work in the subspace `↥(Uc ∪ Vc)`, whose pieces `Uc`, `Vc` are open and cover it
  have hUo' : IsOpen {y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc} := hUo.preimage continuous_subtype_val
  have hVo' : IsOpen {y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc} := hVo.preimage continuous_subtype_val
  have hcov' : {y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc} ∪ {y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc}
      = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      rcases y.2 with h | h
      · exact Or.inl h
      · exact Or.inr h
  -- transport the three vanishing hypotheses to the subspace
  have hU' : ∀ k : ℕ, k ≤ J → Subsingleton ↥(Work.Serre.mvCohU (TopCat.of ↥(Uc ∪ Vc))
      {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} {y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc} k) :=
    fun k hk => Work.Serre.subsingleton_relCoh_twoSubset A Uc Vc Uc (fun _ hx => Or.inl hx) k
      (hU k hk)
  have hV' : ∀ k : ℕ, k ≤ J → Subsingleton ↥(Work.Serre.mvCohV (TopCat.of ↥(Uc ∪ Vc))
      {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} {y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc} k) :=
    fun k hk => Work.Serre.subsingleton_relCoh_twoSubset A Uc Vc Vc (fun _ hx => Or.inr hx) k
      (hV k hk)
  have hUV' : ∀ k : ℕ, k ≤ J → Subsingleton ↥(Work.Serre.mvCohUV (TopCat.of ↥(Uc ∪ Vc))
      {y : ↥(Uc ∪ Vc) | (y : X) ∈ A} {y : ↥(Uc ∪ Vc) | (y : X) ∈ Uc}
      {y : ↥(Uc ∪ Vc) | (y : X) ∈ Vc} k) :=
    fun k hk => Work.Serre.subsingleton_relCoh_twoSubset A Uc Vc (Uc ∩ Vc)
      (fun _ hy => Or.inl hy.1) k (hUV k hk)
  exact relCoh_vanish_union_of_openCover _ _ _ hUo' hVo' hcov' J hU' hV' hUV'

end

end Work.RatHurewicz
