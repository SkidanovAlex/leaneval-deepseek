import Mathlib
import Submission.Work.Serre.five_lemma_LES_mid_shift
import Submission.Work.Serre.les_shift

/-!
# The *bounded* five lemma for two long exact sequences

We consider two long exact sequences of `ℚ`-modules indexed by `ℕ`,
```
⋯ ⟶ M₁ k --F₁--> P₁ k --G₁--> Q₁ k --δ₁--> M₁ (k+1) ⟶ ⋯
⋯ ⟶ M₂ k --F₂--> P₂ k --G₂--> Q₂ k --δ₂--> M₂ (k+1) ⟶ ⋯
```
and a ladder of morphisms `TM k : M₁ k ⟶ M₂ (k+n)`, `TP k`, `TQ k` commuting with `F`, `G` and
`δ` (up to the canonical identification `M₂ ((k+1)+n) ≅ M₂ (k+n+1)` forced by the shift `n`).

The classical five lemma (`Work.Serre.five_lemma_LES_mid_shift`) concludes `IsIso (TP (k+1))` for
all `k` from the *global* hypotheses that every `TM k` and every `TQ k` is an isomorphism.  The
point of the present file is that this is wasteful: the diagram chase producing `IsIso (TP (k+1))`
only ever evaluates `TM` at the indices `k+1` and `k+2`, and `TQ` at the indices `k` and `k+1`
(see `fiveLemma_LES_mid_at` below, whose hypotheses are exactly these four `IsIso` facts).  Hence if
`TM` and `TQ` are isomorphisms only up to index `K+1`, one still gets `IsIso (TP (k+1))` for every
`k` with `k+1 ≤ K` --- because then `k+1, k+2 ≤ K+1` and `k, k+1 ≤ K+1`.  This is the shape needed
when the ladder is only known to be an isomorphism in a bounded range of degrees; the shift `n` is
handled by reindexing the second sequence along `k ↦ k+n` (`Work.Serre.les_shift`), exactly as in
`five_lemma_LES_mid_shift`.

## Contents

* `fiveLemma_LES_mid_at` -- the unshifted five lemma at a single spot, with only the four `IsIso`
  hypotheses the chase actually uses;
* `boundedFiveLemmaLES` -- the requested bounded, shifted statement, obtained by reindexing the
  second exact sequence by `n` and applying `fiveLemma_LES_mid_at` at spot `k`.
-/

namespace Work.Serre

/-- **The five lemma for two long exact sequences, at a single spot.**

Given two long exact sequences (exactness expressed by the three conditions `e₁`, `e₂`, `e₃` at
`M`, `P`, `Q`) and a ladder of morphisms between them commuting with `F`, `G` and `δ`, if the outer
vertical maps `TM (k+1)`, `TM (k+2)`, `TQ k` and `TQ (k+1)` are isomorphisms, then so is the middle
vertical map `TP (k+1)`.

This is `fiveLemma_LES_mid` with the `IsIso` hypotheses pruned to the four instances that the
diagram chase actually uses; the proof is that chase. -/
theorem fiveLemma_LES_mid_at {M₁ P₁ Q₁ M₂ P₂ Q₂ : ℕ → ModuleCat ℚ}
    (F₁ : ∀ k, M₁ k ⟶ P₁ k) (G₁ : ∀ k, P₁ k ⟶ Q₁ k) (δ₁ : ∀ k, Q₁ k ⟶ M₁ (k + 1))
    (F₂ : ∀ k, M₂ k ⟶ P₂ k) (G₂ : ∀ k, P₂ k ⟶ Q₂ k) (δ₂ : ∀ k, Q₂ k ⟶ M₂ (k + 1))
    (e₂₁ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (F₁ k))
      = LinearMap.ker (ModuleCat.Hom.hom (G₁ k)))
    (e₃₁ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (G₁ k))
      = LinearMap.ker (ModuleCat.Hom.hom (δ₁ k)))
    (e₁₁ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (δ₁ k))
      = LinearMap.ker (ModuleCat.Hom.hom (F₁ (k + 1))))
    (e₂₂ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (F₂ k))
      = LinearMap.ker (ModuleCat.Hom.hom (G₂ k)))
    (e₃₂ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (G₂ k))
      = LinearMap.ker (ModuleCat.Hom.hom (δ₂ k)))
    (e₁₂ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (δ₂ k))
      = LinearMap.ker (ModuleCat.Hom.hom (F₂ (k + 1))))
    (TM : ∀ k, M₁ k ⟶ M₂ k) (TP : ∀ k, P₁ k ⟶ P₂ k) (TQ : ∀ k, Q₁ k ⟶ Q₂ k)
    (hF : ∀ k, CategoryTheory.CategoryStruct.comp (F₁ k) (TP k)
      = CategoryTheory.CategoryStruct.comp (TM k) (F₂ k))
    (hG : ∀ k, CategoryTheory.CategoryStruct.comp (G₁ k) (TQ k)
      = CategoryTheory.CategoryStruct.comp (TP k) (G₂ k))
    (hδ : ∀ k, CategoryTheory.CategoryStruct.comp (δ₁ k) (TM (k + 1))
      = CategoryTheory.CategoryStruct.comp (TQ k) (δ₂ k))
    (k : ℕ) (hiTM₁ : CategoryTheory.IsIso (TM (k + 1)))
    (hiTM₂ : CategoryTheory.IsIso (TM (k + 2)))
    (hiTQ₀ : CategoryTheory.IsIso (TQ k)) (hiTQ₁ : CategoryTheory.IsIso (TQ (k + 1))) :
    CategoryTheory.IsIso (TP (k + 1)) := by
  -- bijectivity of the four vertical maps that occur
  have hTM₁ : Function.Bijective (ModuleCat.Hom.hom (TM (k + 1))) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective (TM (k + 1))).mp hiTM₁
  have hTM₂ : Function.Bijective (ModuleCat.Hom.hom (TM (k + 2))) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective (TM (k + 2))).mp hiTM₂
  have hTQ₁ : Function.Bijective (ModuleCat.Hom.hom (TQ (k + 1))) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective (TQ (k + 1))).mp hiTQ₁
  have hTQ₀ : Function.Bijective (ModuleCat.Hom.hom (TQ k)) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective (TQ k)).mp hiTQ₀
  -- the three squares, elementwise
  have hF_ap : ∀ y : M₁ (k + 1),
      (ModuleCat.Hom.hom (TP (k + 1))) ((ModuleCat.Hom.hom (F₁ (k + 1))) y)
        = (ModuleCat.Hom.hom (F₂ (k + 1))) ((ModuleCat.Hom.hom (TM (k + 1))) y) := by
    intro y
    have h := congrArg ModuleCat.Hom.hom (hF (k + 1))
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
    exact DFunLike.congr_fun h y
  have hG_ap : ∀ y : P₁ (k + 1),
      (ModuleCat.Hom.hom (TQ (k + 1))) ((ModuleCat.Hom.hom (G₁ (k + 1))) y)
        = (ModuleCat.Hom.hom (G₂ (k + 1))) ((ModuleCat.Hom.hom (TP (k + 1))) y) := by
    intro y
    have h := congrArg ModuleCat.Hom.hom (hG (k + 1))
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
    exact DFunLike.congr_fun h y
  have hδ_ap : ∀ y : Q₁ k,
      (ModuleCat.Hom.hom (TM (k + 1))) ((ModuleCat.Hom.hom (δ₁ k)) y)
        = (ModuleCat.Hom.hom (δ₂ k)) ((ModuleCat.Hom.hom (TQ k)) y) := by
    intro y
    have h := congrArg ModuleCat.Hom.hom (hδ k)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
    exact DFunLike.congr_fun h y
  have hδ_ap' : ∀ y : Q₁ (k + 1),
      (ModuleCat.Hom.hom (TM (k + 2))) ((ModuleCat.Hom.hom (δ₁ (k + 1))) y)
        = (ModuleCat.Hom.hom (δ₂ (k + 1))) ((ModuleCat.Hom.hom (TQ (k + 1))) y) := by
    intro y
    have h := congrArg ModuleCat.Hom.hom (hδ (k + 1))
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
    exact DFunLike.congr_fun h y
  refine (CategoryTheory.ConcreteCategory.isIso_iff_bijective (TP (k + 1))).mpr ⟨?_, ?_⟩
  · -- injectivity of `TP (k+1)`
    have key : ∀ x : P₁ (k + 1), (ModuleCat.Hom.hom (TP (k + 1))) x = 0 → x = 0 := by
      intro x hx
      have h1 : (ModuleCat.Hom.hom (TQ (k + 1))) ((ModuleCat.Hom.hom (G₁ (k + 1))) x) = 0 := by
        rw [hG_ap, hx, map_zero]
      have h2 : (ModuleCat.Hom.hom (G₁ (k + 1))) x = 0 := by
        have h1b : (ModuleCat.Hom.hom (TQ (k + 1))) ((ModuleCat.Hom.hom (G₁ (k + 1))) x)
            = (ModuleCat.Hom.hom (TQ (k + 1))) 0 := by rw [h1, map_zero]
        exact hTQ₁.1 h1b
      have h3 : x ∈ LinearMap.range (ModuleCat.Hom.hom (F₁ (k + 1))) := by
        rw [e₂₁ (k + 1)]
        simpa [LinearMap.mem_ker] using h2
      obtain ⟨y, hy⟩ : ∃ y, (ModuleCat.Hom.hom (F₁ (k + 1))) y = x := by
        simpa [LinearMap.mem_range] using h3
      have h4 : (ModuleCat.Hom.hom (F₂ (k + 1))) ((ModuleCat.Hom.hom (TM (k + 1))) y) = 0 := by
        rw [← hF_ap y, hy, hx]
      have h5 : (ModuleCat.Hom.hom (TM (k + 1))) y
          ∈ LinearMap.range (ModuleCat.Hom.hom (δ₂ k)) := by
        rw [e₁₂ k]
        simpa [LinearMap.mem_ker] using h4
      obtain ⟨w, hw⟩ : ∃ w, (ModuleCat.Hom.hom (δ₂ k)) w
          = (ModuleCat.Hom.hom (TM (k + 1))) y := by
        simpa [LinearMap.mem_range] using h5
      obtain ⟨u, hu⟩ : ∃ u, (ModuleCat.Hom.hom (TQ k)) u = w := hTQ₀.2 w
      have h6 : (ModuleCat.Hom.hom (TM (k + 1))) ((ModuleCat.Hom.hom (δ₁ k)) u)
          = (ModuleCat.Hom.hom (TM (k + 1))) y := by
        rw [hδ_ap u, hu, hw]
      have h7 : (ModuleCat.Hom.hom (δ₁ k)) u = y := hTM₁.1 h6
      have h8 : (ModuleCat.Hom.hom (F₁ (k + 1))) y = 0 := by
        have h8' : y ∈ LinearMap.ker (ModuleCat.Hom.hom (F₁ (k + 1))) := by
          rw [← e₁₁ k]
          exact LinearMap.mem_range.mpr ⟨u, h7⟩
        simpa [LinearMap.mem_ker] using h8'
      rw [← hy, h8]
    intro x y hxy
    have hsub : (ModuleCat.Hom.hom (TP (k + 1))) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (key (x - y) hsub)
  · -- surjectivity of `TP (k+1)`
    intro p
    obtain ⟨q, hq⟩ := hTQ₁.2 ((ModuleCat.Hom.hom (G₂ (k + 1))) p)
    have h1 : (ModuleCat.Hom.hom (δ₂ (k + 1))) ((ModuleCat.Hom.hom (TQ (k + 1))) q) = 0 := by
      rw [hq]
      have h1' : (ModuleCat.Hom.hom (G₂ (k + 1))) p
          ∈ LinearMap.ker (ModuleCat.Hom.hom (δ₂ (k + 1))) := by
        rw [← e₃₂ (k + 1)]
        exact LinearMap.mem_range.mpr ⟨p, rfl⟩
      simpa [LinearMap.mem_ker] using h1'
    have h2 : (ModuleCat.Hom.hom (TM (k + 2))) ((ModuleCat.Hom.hom (δ₁ (k + 1))) q) = 0 := by
      rw [hδ_ap' q, h1]
    have h3 : (ModuleCat.Hom.hom (δ₁ (k + 1))) q = 0 := by
      have h2b : (ModuleCat.Hom.hom (TM (k + 2))) ((ModuleCat.Hom.hom (δ₁ (k + 1))) q)
          = (ModuleCat.Hom.hom (TM (k + 2))) 0 := by rw [h2, map_zero]
      exact hTM₂.1 h2b
    have h4 : q ∈ LinearMap.range (ModuleCat.Hom.hom (G₁ (k + 1))) := by
      rw [e₃₁ (k + 1)]
      simpa [LinearMap.mem_ker] using h3
    obtain ⟨x, hx⟩ : ∃ x, (ModuleCat.Hom.hom (G₁ (k + 1))) x = q := by
      simpa [LinearMap.mem_range] using h4
    have h5 : (ModuleCat.Hom.hom (G₂ (k + 1))) ((ModuleCat.Hom.hom (TP (k + 1))) x)
        = (ModuleCat.Hom.hom (G₂ (k + 1))) p := by
      rw [← hG_ap x, hx, hq]
    have h6 : p - (ModuleCat.Hom.hom (TP (k + 1))) x
        ∈ LinearMap.range (ModuleCat.Hom.hom (F₂ (k + 1))) := by
      rw [e₂₂ (k + 1)]
      have h6' : (ModuleCat.Hom.hom (G₂ (k + 1)))
          (p - (ModuleCat.Hom.hom (TP (k + 1))) x) = 0 := by
        rw [map_sub, h5, sub_self]
      simpa [LinearMap.mem_ker] using h6'
    obtain ⟨y, hy⟩ : ∃ y, (ModuleCat.Hom.hom (F₂ (k + 1))) y
        = p - (ModuleCat.Hom.hom (TP (k + 1))) x := by
      simpa [LinearMap.mem_range] using h6
    obtain ⟨y', hy'⟩ : ∃ y', (ModuleCat.Hom.hom (TM (k + 1))) y' = y := hTM₁.2 y
    refine ⟨x + (ModuleCat.Hom.hom (F₁ (k + 1))) y', ?_⟩
    rw [map_add, hF_ap y', hy', hy]
    abel

/-- **The bounded five lemma for two long exact sequences, with a shift.**

If `TM k : M₁ k ⟶ M₂ (k+n)` and `TQ k : Q₁ k ⟶ Q₂ (k+n)` are isomorphisms for all `k ≤ K+1`, then
`TP (k+1)` is an isomorphism for all `k` with `k+1 ≤ K`.  (Recall that the five lemma at spot `k+1`
consumes `TM` at `k+1` and `k+2` and `TQ` at `k` and `k+1`, all of which are `≤ K+1` under the
bound `k+1 ≤ K`.) -/
theorem boundedFiveLemmaLES (n K : ℕ) {M₁ P₁ Q₁ M₂ P₂ Q₂ : ℕ → ModuleCat ℚ}
    (F₁ : ∀ k, M₁ k ⟶ P₁ k) (G₁ : ∀ k, P₁ k ⟶ Q₁ k) (δ₁ : ∀ k, Q₁ k ⟶ M₁ (k + 1))
    (F₂ : ∀ k, M₂ k ⟶ P₂ k) (G₂ : ∀ k, P₂ k ⟶ Q₂ k) (δ₂ : ∀ k, Q₂ k ⟶ M₂ (k + 1))
    (e₂₁ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (F₁ k)) = LinearMap.ker (ModuleCat.Hom.hom (G₁ k)))
    (e₃₁ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (G₁ k)) = LinearMap.ker (ModuleCat.Hom.hom (δ₁ k)))
    (e₁₁ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (δ₁ k)) = LinearMap.ker (ModuleCat.Hom.hom (F₁ (k + 1))))
    (e₂₂ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (F₂ k)) = LinearMap.ker (ModuleCat.Hom.hom (G₂ k)))
    (e₃₂ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (G₂ k)) = LinearMap.ker (ModuleCat.Hom.hom (δ₂ k)))
    (e₁₂ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (δ₂ k)) = LinearMap.ker (ModuleCat.Hom.hom (F₂ (k + 1))))
    (TM : ∀ k, M₁ k ⟶ M₂ (k + n)) (TP : ∀ k, P₁ k ⟶ P₂ (k + n)) (TQ : ∀ k, Q₁ k ⟶ Q₂ (k + n))
    (hF : ∀ k, CategoryTheory.CategoryStruct.comp (F₁ k) (TP k) = CategoryTheory.CategoryStruct.comp (TM k) (F₂ (k + n)))
    (hG : ∀ k, CategoryTheory.CategoryStruct.comp (G₁ k) (TQ k) = CategoryTheory.CategoryStruct.comp (TP k) (G₂ (k + n)))
    (hδ : ∀ k, CategoryTheory.CategoryStruct.comp (δ₁ k) (TM (k + 1)) = CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (TQ k) (δ₂ (k + n))) (CategoryTheory.eqToHom (by congr 1; omega)))
    (hM : ∀ k, k ≤ K + 1 → CategoryTheory.IsIso (TM k))
    (hQ : ∀ k, k ≤ K + 1 → CategoryTheory.IsIso (TQ k)) :
    ∀ k, k + 1 ≤ K → CategoryTheory.IsIso (TP (k + 1)) := by
  intro k hk
  -- reindex the second sequence by `k ↦ k + n`, so that it is indexed like the first one
  let δ₂' : ∀ j, Q₂ (j + n) ⟶ M₂ ((j + 1) + n) := fun j =>
    CategoryTheory.CategoryStruct.comp (δ₂ (j + n))
      (CategoryTheory.eqToHom (congrArg M₂ (by omega : j + n + 1 = (j + 1) + n)))
  -- reindexing preserves exactness
  obtain ⟨e₂₂', e₃₂', e₁₂'⟩ := les_shift n F₂ G₂ δ₂ e₂₂ e₃₂ e₁₂
  -- the connecting maps of the ladder commute with the shift, up to associativity
  have hδ' : ∀ j, CategoryTheory.CategoryStruct.comp (δ₁ j) (TM (j + 1))
      = CategoryTheory.CategoryStruct.comp (TQ j) (δ₂' j) := by
    intro j
    rw [hδ j]
    dsimp only [δ₂']
    simp only [CategoryTheory.Category.assoc]
  -- the single-spot five lemma for the reindexed second sequence
  exact fiveLemma_LES_mid_at (M₂ := fun j => M₂ (j + n)) (P₂ := fun j => P₂ (j + n))
    (Q₂ := fun j => Q₂ (j + n)) F₁ G₁ δ₁ (fun j => F₂ (j + n)) (fun j => G₂ (j + n)) δ₂'
    e₂₁ e₃₁ e₁₁ e₂₂' e₃₂' e₁₂' TM TP TQ hF hG hδ' k
    (hM (k + 1) (by omega)) (hM (k + 2) (by omega))
    (hQ k (by omega)) (hQ (k + 1) (by omega))

end Work.Serre
