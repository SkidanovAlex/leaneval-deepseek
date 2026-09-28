import Mathlib
import Submission.Work.Serre.boundedFiveLemmaLES

/-!
# The five lemma for two long exact sequences, at the `M`-slot

Given two long exact sequences of `ℚ`-modules
```
⋯ ⟶ M₁ k --F₁--> P₁ k --G₁--> Q₁ k --δ₁--> M₁ (k+1) ⟶ ⋯
⋯ ⟶ M₂ k --F₂--> P₂ k --G₂--> Q₂ k --δ₂--> M₂ (k+1) ⟶ ⋯
```
and a ladder `TM, TP, TQ` commuting with `F`, `G`, `δ`, the five lemma at the spot `M₁ (k+1)`
(whose five-term window is `P₁ k → Q₁ k → M₁ (k+1) → P₁ (k+1) → Q₁ (k+1)`) concludes that
`TM (k+1)` is an isomorphism from the four outer vertical maps `TP k`, `TQ k`, `TP (k+1)`,
`TQ (k+1)`.

This is the mirror image of `Work.Serre.fiveLemma_LES_mid_at`, which provides the same conclusion
for the `P`-slot map `TP (k+1)` from the outer maps `TM (k+1)`, `TM (k+2)`, `TQ k`, `TQ (k+1)`;
here the `M`-slot plays the role of the middle term, so the chase is the one dual to it.  The proof
below is that diagram chase, carried out elementwise on the underlying linear maps.
-/

namespace Work.Serre

theorem fiveLemma_LES_first {M₁ P₁ Q₁ M₂ P₂ Q₂ : ℕ → ModuleCat ℚ}
    (F₁ : ∀ k, M₁ k ⟶ P₁ k) (G₁ : ∀ k, P₁ k ⟶ Q₁ k) (δ₁ : ∀ k, Q₁ k ⟶ M₁ (k + 1))
    (F₂ : ∀ k, M₂ k ⟶ P₂ k) (G₂ : ∀ k, P₂ k ⟶ Q₂ k) (δ₂ : ∀ k, Q₂ k ⟶ M₂ (k + 1))
    (e₂₁ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (F₁ k)) = LinearMap.ker (ModuleCat.Hom.hom (G₁ k)))
    (e₃₁ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (G₁ k)) = LinearMap.ker (ModuleCat.Hom.hom (δ₁ k)))
    (e₁₁ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (δ₁ k)) = LinearMap.ker (ModuleCat.Hom.hom (F₁ (k + 1))))
    (e₂₂ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (F₂ k)) = LinearMap.ker (ModuleCat.Hom.hom (G₂ k)))
    (e₃₂ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (G₂ k)) = LinearMap.ker (ModuleCat.Hom.hom (δ₂ k)))
    (e₁₂ : ∀ k, LinearMap.range (ModuleCat.Hom.hom (δ₂ k)) = LinearMap.ker (ModuleCat.Hom.hom (F₂ (k + 1))))
    (TM : ∀ k, M₁ k ⟶ M₂ k) (TP : ∀ k, P₁ k ⟶ P₂ k) (TQ : ∀ k, Q₁ k ⟶ Q₂ k)
    (hF : ∀ k, CategoryTheory.CategoryStruct.comp (F₁ k) (TP k) = CategoryTheory.CategoryStruct.comp (TM k) (F₂ k))
    (hG : ∀ k, CategoryTheory.CategoryStruct.comp (G₁ k) (TQ k) = CategoryTheory.CategoryStruct.comp (TP k) (G₂ k))
    (hδ : ∀ k, CategoryTheory.CategoryStruct.comp (δ₁ k) (TM (k + 1)) = CategoryTheory.CategoryStruct.comp (TQ k) (δ₂ k))
    (k : ℕ) (hP₀ : CategoryTheory.IsIso (TP k)) (hQ₀ : CategoryTheory.IsIso (TQ k))
    (hP₁ : CategoryTheory.IsIso (TP (k + 1))) (hQ₁ : CategoryTheory.IsIso (TQ (k + 1))) :
    CategoryTheory.IsIso (TM (k + 1)) := by
  -- bijectivity of the four vertical maps that the chase uses
  have hTP₀ : Function.Bijective (ModuleCat.Hom.hom (TP k)) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective (TP k)).mp hP₀
  have hTP₁ : Function.Bijective (ModuleCat.Hom.hom (TP (k + 1))) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective (TP (k + 1))).mp hP₁
  have hTQ₀ : Function.Bijective (ModuleCat.Hom.hom (TQ k)) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective (TQ k)).mp hQ₀
  have hTQ₁ : Function.Bijective (ModuleCat.Hom.hom (TQ (k + 1))) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective (TQ (k + 1))).mp hQ₁
  -- the three squares, elementwise
  have hF_ap : ∀ y : M₁ (k + 1),
      (ModuleCat.Hom.hom (TP (k + 1))) ((ModuleCat.Hom.hom (F₁ (k + 1))) y)
        = (ModuleCat.Hom.hom (F₂ (k + 1))) ((ModuleCat.Hom.hom (TM (k + 1))) y) := by
    intro y
    have h := congrArg ModuleCat.Hom.hom (hF (k + 1))
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
    exact DFunLike.congr_fun h y
  have hG_ap : ∀ y : P₁ k,
      (ModuleCat.Hom.hom (TQ k)) ((ModuleCat.Hom.hom (G₁ k)) y)
        = (ModuleCat.Hom.hom (G₂ k)) ((ModuleCat.Hom.hom (TP k)) y) := by
    intro y
    have h := congrArg ModuleCat.Hom.hom (hG k)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
    exact DFunLike.congr_fun h y
  have hG_ap₁ : ∀ y : P₁ (k + 1),
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
  refine (CategoryTheory.ConcreteCategory.isIso_iff_bijective (TM (k + 1))).mpr ⟨?_, ?_⟩
  · -- injectivity of `TM (k+1)`
    have key : ∀ x : M₁ (k + 1), (ModuleCat.Hom.hom (TM (k + 1))) x = 0 → x = 0 := by
      intro x hx
      -- `F₁ (k+1) x = 0` because `TP (k+1)` is injective
      have h1 : (ModuleCat.Hom.hom (F₁ (k + 1))) x = 0 := by
        apply hTP₁.1
        rw [hF_ap x, hx]; simp
      -- hence `x = δ₁ k q`
      have h2 : x ∈ LinearMap.range (ModuleCat.Hom.hom (δ₁ k)) := by
        rw [e₁₁ k]
        simpa [LinearMap.mem_ker] using h1
      obtain ⟨q, hq⟩ : ∃ q, (ModuleCat.Hom.hom (δ₁ k)) q = x := by
        simpa [LinearMap.mem_range] using h2
      -- `δ₂ k (TQ k q) = 0`, so `TQ k q = G₂ k p`
      have h3 : (ModuleCat.Hom.hom (δ₂ k)) ((ModuleCat.Hom.hom (TQ k)) q) = 0 := by
        rw [← hδ_ap q, hq, hx]
      have h4 : (ModuleCat.Hom.hom (TQ k)) q ∈ LinearMap.range (ModuleCat.Hom.hom (G₂ k)) := by
        rw [e₃₂ k]
        simpa [LinearMap.mem_ker] using h3
      obtain ⟨p, hp⟩ : ∃ p, (ModuleCat.Hom.hom (G₂ k)) p = (ModuleCat.Hom.hom (TQ k)) q := by
        simpa [LinearMap.mem_range] using h4
      -- lift `p` along the surjective `TP k`
      obtain ⟨p', hp'⟩ : ∃ p', (ModuleCat.Hom.hom (TP k)) p' = p := hTP₀.2 p
      have h5 : (ModuleCat.Hom.hom (TQ k)) ((ModuleCat.Hom.hom (G₁ k)) p')
          = (ModuleCat.Hom.hom (TQ k)) q := by
        rw [hG_ap p', hp', hp]
      have h6 : (ModuleCat.Hom.hom (G₁ k)) p' = q := hTQ₀.1 h5
      have h7 : (ModuleCat.Hom.hom (δ₁ k)) q = 0 := by
        have h7' : q ∈ LinearMap.ker (ModuleCat.Hom.hom (δ₁ k)) := by
          rw [← e₃₁ k]
          exact LinearMap.mem_range.mpr ⟨p', h6⟩
        simpa [LinearMap.mem_ker] using h7'
      rw [← hq, h7]
    intro x y hxy
    have hsub : (ModuleCat.Hom.hom (TM (k + 1))) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (key (x - y) hsub)
  · -- surjectivity of `TM (k+1)`
    intro y
    -- choose `p` with `TP (k+1) p = F₂ (k+1) y`
    obtain ⟨p, hp⟩ : ∃ p, (ModuleCat.Hom.hom (TP (k + 1))) p
        = (ModuleCat.Hom.hom (F₂ (k + 1))) y := hTP₁.2 _
    have h1 : (ModuleCat.Hom.hom (TQ (k + 1))) ((ModuleCat.Hom.hom (G₁ (k + 1))) p) = 0 := by
      rw [hG_ap₁ p, hp]
      have h1' : (ModuleCat.Hom.hom (F₂ (k + 1))) y
          ∈ LinearMap.ker (ModuleCat.Hom.hom (G₂ (k + 1))) := by
        rw [← e₂₂ (k + 1)]
        exact LinearMap.mem_range.mpr ⟨y, rfl⟩
      simpa [LinearMap.mem_ker] using h1'
    have h2 : (ModuleCat.Hom.hom (G₁ (k + 1))) p = 0 := by
      have h2b : (ModuleCat.Hom.hom (TQ (k + 1))) ((ModuleCat.Hom.hom (G₁ (k + 1))) p)
          = (ModuleCat.Hom.hom (TQ (k + 1))) 0 := by rw [h1, map_zero]
      exact hTQ₁.1 h2b
    -- hence `p = F₁ (k+1) x₀`
    have h3 : p ∈ LinearMap.range (ModuleCat.Hom.hom (F₁ (k + 1))) := by
      rw [e₂₁ (k + 1)]
      simpa [LinearMap.mem_ker] using h2
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, (ModuleCat.Hom.hom (F₁ (k + 1))) x₀ = p := by
      simpa [LinearMap.mem_range] using h3
    have h4 : (ModuleCat.Hom.hom (F₂ (k + 1))) ((ModuleCat.Hom.hom (TM (k + 1))) x₀)
        = (ModuleCat.Hom.hom (F₂ (k + 1))) y := by
      rw [← hF_ap x₀, hx₀, hp]
    -- the difference lies in the image of the connecting map `δ₂ k`
    have h5 : y - (ModuleCat.Hom.hom (TM (k + 1))) x₀
        ∈ LinearMap.range (ModuleCat.Hom.hom (δ₂ k)) := by
      rw [e₁₂ k]
      have h5' : (ModuleCat.Hom.hom (F₂ (k + 1)))
          (y - (ModuleCat.Hom.hom (TM (k + 1))) x₀) = 0 := by
        rw [map_sub, h4, sub_self]
      simpa [LinearMap.mem_ker] using h5'
    obtain ⟨w, hw⟩ : ∃ w, (ModuleCat.Hom.hom (δ₂ k)) w
        = y - (ModuleCat.Hom.hom (TM (k + 1))) x₀ := by
      simpa [LinearMap.mem_range] using h5
    obtain ⟨w', hw'⟩ : ∃ w', (ModuleCat.Hom.hom (TQ k)) w' = w := hTQ₀.2 w
    refine ⟨x₀ + (ModuleCat.Hom.hom (δ₁ k)) w', ?_⟩
    rw [map_add, hδ_ap w', hw', hw]
    abel

end Work.Serre
