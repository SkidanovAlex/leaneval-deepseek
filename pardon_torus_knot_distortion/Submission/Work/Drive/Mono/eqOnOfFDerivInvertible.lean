import Mathlib

/-!
# Uniqueness of a lift across a local diffeomorphism on a preconnected set

If `f : ℝ × ℝ → ℝ × ℝ` is strictly differentiable at every point with invertible derivative, then
`f` is a local homeomorphism (the inverse function theorem, in the form of the workspace's
`HasStrictFDerivAt.toOpenPartialHomeomorph`: `f` is injective on a neighbourhood of every point).
Consequently, if two continuous maps `q₁ q₂ : ℝ → ℝ × ℝ` agree at `0` and have the same image under
`f` on a preconnected set `K` containing `0`, then they agree on all of `K`.

The proof shows that `{t ∈ K | q₁ t = q₂ t}` is both open and closed inside `K`: closed because
`q₁ - q₂` is continuous, and open because near a coincidence point `t` both `q₁` and `q₂` take
values in a *single* neighbourhood on which `f` is injective, so `f (q₁ s) = f (q₂ s)` forces
`q₁ s = q₂ s`.  Preconnectedness of `K` then gives global agreement.
-/

open Filter Set
open scoped Topology

namespace Work.Drive.Mono

theorem eqOnOfFDerivInvertible (f : ℝ × ℝ → ℝ × ℝ)
    (hd : ∀ x, HasStrictFDerivAt f (fderiv ℝ f x) x)
    {q₁ q₂ : ℝ → ℝ × ℝ} {K : Set ℝ} (hK : IsPreconnected K) (h0 : (0:ℝ) ∈ K)
    (h1 : ContinuousOn q₁ K) (h2 : ContinuousOn q₂ K) (h00 : q₁ 0 = q₂ 0)
    (hinv : ∀ t ∈ K, (fderiv ℝ f (q₁ t)).IsInvertible)
    (heq : ∀ t ∈ K, f (q₁ t) = f (q₂ t)) : ∀ t ∈ K, q₁ t = q₂ t := by
  -- local injectivity of `f` at every point of the form `q₁ t`, `t ∈ K`
  have hloc : ∀ t ∈ K, ∃ U : Set (ℝ × ℝ), IsOpen U ∧ q₁ t ∈ U ∧ Set.InjOn f U := by
    intro t ht
    obtain ⟨e, he⟩ := hinv t ht
    have hstrict : HasStrictFDerivAt f (e : ℝ × ℝ →L[ℝ] ℝ × ℝ) (q₁ t) := by
      rw [he]; exact hd (q₁ t)
    exact ⟨(hstrict.toOpenPartialHomeomorph f).source,
      (hstrict.toOpenPartialHomeomorph f).open_source,
      hstrict.mem_toOpenPartialHomeomorph_source,
      (hstrict.toOpenPartialHomeomorph f).injOn⟩
  -- the coincidence set, as a subset of the subtype `K`
  set U : Set ↥K := {t | q₁ (t : ℝ) = q₂ (t : ℝ)} with hUdef
  have hcont₁ : Continuous fun t : ↥K => q₁ (t : ℝ) := h1.domRestrict
  have hcont₂ : Continuous fun t : ↥K => q₂ (t : ℝ) := h2.domRestrict
  have hclopen : IsClopen U := by
    constructor
    · exact isClosed_eq hcont₁ hcont₂
    · rw [isOpen_iff_mem_nhds]
      intro t ht
      have ht' : q₁ (t : ℝ) = q₂ (t : ℝ) := ht
      obtain ⟨U₀, hU₀open, htU₀, hU₀inj⟩ := hloc t t.2
      have htU₀₂ : q₂ (t : ℝ) ∈ U₀ := by rw [← ht']; exact htU₀
      have hmem₁ : {t' : ↥K | q₁ (t' : ℝ) ∈ U₀} ∈ 𝓝 t :=
        (hcont₁.isOpen_preimage U₀ hU₀open).mem_nhds htU₀
      have hmem₂ : {t' : ↥K | q₂ (t' : ℝ) ∈ U₀} ∈ 𝓝 t :=
        (hcont₂.isOpen_preimage U₀ hU₀open).mem_nhds htU₀₂
      refine Filter.mem_of_superset (Filter.inter_mem hmem₁ hmem₂) ?_
      rintro t' ⟨hx, hy⟩
      exact hU₀inj hx hy (heq t'.1 t'.2)
  have hpre : PreconnectedSpace ↥K := isPreconnected_iff_preconnectedSpace.mp hK
  have huniv : (Set.univ : Set ↥K) ⊆ U :=
    hpre.isPreconnected_univ.subset_isClopen hclopen ⟨⟨0, h0⟩, by simp [hUdef, h00]⟩
  intro t ht
  exact huniv (Set.mem_univ ⟨t, ht⟩)

end Work.Drive.Mono
