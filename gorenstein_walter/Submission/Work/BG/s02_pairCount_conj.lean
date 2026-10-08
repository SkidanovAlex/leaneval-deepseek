import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.s02_l22c1Defs

namespace Work.BG

/-- **Conjugation invariance of the pair count.**  If `X` is conjugation-invariant
(`∀ g x, x ∈ X → g*x*g⁻¹ ∈ X`) then the number of pairs in `X × X` with product `g` is
invariant under `g ↦ h*g*h⁻¹`: the map `(x,y) ↦ (h*x*h⁻¹, h*y*h⁻¹)` is a bijection between
the two filtered pair sets. -/
theorem s02_pairCount_conj {G : Type} [Group G] [Fintype G] (X : Finset G)
    (hX : ∀ g x : G, x ∈ X → g * x * g⁻¹ ∈ X) (g h : G) :
    (Work.BG.pairSet X (h * g * h⁻¹)).card = (Work.BG.pairSet X g).card := by
  classical
  -- Conjugation by `h⁻¹` is a bijection from pairs of `X` with product `h * g * h⁻¹`
  -- onto pairs of `X` with product `g`; it preserves membership in `X` by invariance.
  refine Finset.card_bij (fun (a : G × G) (_ : a ∈ pairSet X (h * g * h⁻¹)) =>
    (h⁻¹ * a.1 * h, h⁻¹ * a.2 * h)) ?_ ?_ ?_
  · intro a ha
    simp only [mem_pairSet] at ha ⊢
    obtain ⟨ha1, ha2, ha3⟩ := ha
    refine ⟨?_, ?_, ?_⟩
    · simpa using hX h⁻¹ a.1 ha1
    · simpa using hX h⁻¹ a.2 ha2
    · have hmul : h⁻¹ * a.1 * h * (h⁻¹ * a.2 * h) = h⁻¹ * (a.1 * a.2) * h := by group
      rw [hmul, ha3]; group
  · intro a ha b hb hab
    simp only [Prod.mk.injEq] at hab
    have h1 : a.1 = b.1 := by
      calc a.1 = h * (h⁻¹ * a.1 * h) * h⁻¹ := by group
        _ = h * (h⁻¹ * b.1 * h) * h⁻¹ := by rw [hab.1]
        _ = b.1 := by group
    have h2 : a.2 = b.2 := by
      calc a.2 = h * (h⁻¹ * a.2 * h) * h⁻¹ := by group
        _ = h * (h⁻¹ * b.2 * h) * h⁻¹ := by rw [hab.2]
        _ = b.2 := by group
    exact Prod.ext h1 h2
  · intro b hb
    simp only [mem_pairSet] at hb
    obtain ⟨hb1, hb2, hb3⟩ := hb
    refine ⟨(h * b.1 * h⁻¹, h * b.2 * h⁻¹), ?_, ?_⟩
    · simp only [mem_pairSet]
      refine ⟨?_, ?_, ?_⟩
      · simpa using hX h b.1 hb1
      · simpa using hX h b.2 hb2
      · have hmul : h * b.1 * h⁻¹ * (h * b.2 * h⁻¹) = h * (b.1 * b.2) * h⁻¹ := by group
        rw [hmul, hb3]
    · exact Prod.ext (by group) (by group)

end Work.BG
