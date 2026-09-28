import Mathlib
import Submission.Work.Serre.les_shift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The five lemma for two long exact sequences, in the middle, with a shift

We consider two long exact sequences of `ℚ`-modules indexed by `ℕ`,
```
⋯ ⟶ M₁ k --F₁--> P₁ k --G₁--> Q₁ k --δ₁--> M₁ (k+1) ⟶ ⋯
⋯ ⟶ M₂ k --F₂--> P₂ k --G₂--> Q₂ k --δ₂--> M₂ (k+1) ⟶ ⋯
```
and a ladder of morphisms `TM k : M₁ k ⟶ M₂ (k+n)`, `TP k`, `TQ k` commuting with `F`, `G` and
`δ` (up to the canonical identification `M₂ ((k+1)+n) ≅ M₂ (k+n+1)` forced by the shift `n`).

If `TM k` and `TQ k` are isomorphisms for all `k`, then `TP k` is an isomorphism for all `k ≥ 1`.

The proof is the classical five lemma diagram chase.  We first prove the general (unshifted) five
lemma `fiveLemma_LES_mid` for two long exact sequences indexed in the same way, then apply it to the
second sequence reindexed by `k ↦ k + n`; the reindexing is `Work.Serre.les_shift`, the statement
that a long exact sequence stays exact after being shifted.  The three transport lemmas about
`eqToHom` below record how `range` and `ker` behave under the canonical isomorphisms comparing
`M a` and `M b` for provably equal indices `a`, `b` -- exactly the bookkeeping needed to move
between the index expressions `k+n+1` and `(k+1)+n`.
-/

namespace Work.Serre

/-- Proof irrelevance for `eqToHom`: only the statement of the equality of objects matters. -/
lemma eqToHom_eqToHom {X Y : ModuleCat ℚ} (h₁ h₂ : X = Y) :
    CategoryTheory.eqToHom h₁ = CategoryTheory.eqToHom h₂ := by
  rw [Subsingleton.elim h₁ h₂]

/-- For provably equal indices `a = b`, the canonical isomorphism `M a ≅ M b` carries the kernel of
a family of linear maps at `a` to the kernel at `b`. -/
lemma map_ker_eqToHom_congrArg {M P : ℕ → ModuleCat ℚ} (F : ∀ k, M k ⟶ P k) {a b : ℕ}
    (h : a = b) :
    (LinearMap.ker (ModuleCat.Hom.hom (F a))).map
        (ModuleCat.Hom.hom (CategoryTheory.eqToHom (congrArg M h)))
      = LinearMap.ker (ModuleCat.Hom.hom (F b)) := by
  subst h
  simp

/-- The underlying linear map of the canonical isomorphism `M a ≅ M b` (`a = b`) is injective. -/
lemma injective_eqToHom_congrArg {M : ℕ → ModuleCat ℚ} {a b : ℕ} (h : a = b) :
    Function.Injective (ModuleCat.Hom.hom (CategoryTheory.eqToHom (congrArg M h))) := by
  subst h
  simp only [CategoryTheory.eqToHom_refl, ModuleCat.hom_id]
  exact fun _ _ hxy => hxy

/-- **The five lemma for two long exact sequences.**  Given two long exact sequences (in the sense
of the three exactness conditions at `M`, `P` and `Q`) and a ladder of morphisms between them
commuting with `F`, `G` and `δ`, if the outer vertical maps `TM k` and `TQ k` are isomorphisms for
all `k`, then the middle vertical maps `TP k` are isomorphisms for all `k ≥ 1`. -/
theorem fiveLemma_LES_mid {M₁ P₁ Q₁ M₂ P₂ Q₂ : ℕ → ModuleCat ℚ}
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
    (hM : ∀ k, CategoryTheory.IsIso (TM k)) (hQ : ∀ k, CategoryTheory.IsIso (TQ k)) :
    ∀ k, CategoryTheory.IsIso (TP (k + 1)) := by
  intro k
  -- bijectivity of the four vertical maps that occur
  have hTM₁ : Function.Bijective (ModuleCat.Hom.hom (TM (k + 1))) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective (TM (k + 1))).mp (hM (k + 1))
  have hTM₂ : Function.Bijective (ModuleCat.Hom.hom (TM (k + 2))) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective (TM (k + 2))).mp (hM (k + 2))
  have hTQ₁ : Function.Bijective (ModuleCat.Hom.hom (TQ (k + 1))) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective (TQ (k + 1))).mp (hQ (k + 1))
  have hTQ₀ : Function.Bijective (ModuleCat.Hom.hom (TQ k)) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective (TQ k)).mp (hQ k)
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

theorem five_lemma_LES_mid_shift {M₁ P₁ Q₁ M₂ P₂ Q₂ : ℕ → ModuleCat ℚ} (n : ℕ)
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
    (TM : ∀ k, M₁ k ⟶ M₂ (k + n)) (TP : ∀ k, P₁ k ⟶ P₂ (k + n)) (TQ : ∀ k, Q₁ k ⟶ Q₂ (k + n))
    (hF : ∀ k, CategoryTheory.CategoryStruct.comp (F₁ k) (TP k) = CategoryTheory.CategoryStruct.comp (TM k) (F₂ (k + n)))
    (hG : ∀ k, CategoryTheory.CategoryStruct.comp (G₁ k) (TQ k) = CategoryTheory.CategoryStruct.comp (TP k) (G₂ (k + n)))
    (hδ : ∀ k, CategoryTheory.CategoryStruct.comp (δ₁ k) (TM (k + 1)) = CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (TQ k) (δ₂ (k + n))) (CategoryTheory.eqToHom (by congr 1; omega)))
    (hM : ∀ k, CategoryTheory.IsIso (TM k)) (hQ : ∀ k, CategoryTheory.IsIso (TQ k)) :
    ∀ k, CategoryTheory.IsIso (TP (k + 1)) := by
  -- the second sequence, reindexed by `k ↦ k + n`
  let δ₂' : ∀ k, Q₂ (k + n) ⟶ M₂ ((k + 1) + n) := fun k =>
    CategoryTheory.CategoryStruct.comp (δ₂ (k + n))
      (CategoryTheory.eqToHom (congrArg M₂ (by omega : k + n + 1 = (k + 1) + n)))
  -- reindexing preserves exactness
  obtain ⟨e₂₂', e₃₂', e₁₂'⟩ := les_shift n F₂ G₂ δ₂ e₂₂ e₃₂ e₁₂
  -- the connecting map of the ramps commutes with the shift, up to associativity
  have hδ' : ∀ k, CategoryTheory.CategoryStruct.comp (δ₁ k) (TM (k + 1))
      = CategoryTheory.CategoryStruct.comp (TQ k) (δ₂' k) := by
    intro k
    rw [hδ k]
    dsimp only [δ₂']
    simp only [CategoryTheory.Category.assoc]
  -- the (unshifted) five lemma for the reindexed second sequence
  exact fiveLemma_LES_mid (M₂ := fun k => M₂ (k + n)) (P₂ := fun k => P₂ (k + n))
    (Q₂ := fun k => Q₂ (k + n)) F₁ G₁ δ₁ (fun k => F₂ (k + n)) (fun k => G₂ (k + n)) δ₂'
    e₂₁ e₃₁ e₁₁ e₂₂' e₃₂' e₁₂' TM TP TQ hF hG hδ' hM hQ

end Work.Serre
