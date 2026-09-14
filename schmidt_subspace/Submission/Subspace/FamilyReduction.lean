import Mathlib
import Submission.Subspace.PairReduction
import Submission.Commons.Analysis.Normed.finite_bounded_int_vectors

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open scoped BigOperators

namespace Submission.Subspace

variable {n : ℕ}

/-! ## Discarding the bounded-height hyperplanes

The height dichotomy gives, for each hyperplane of a family, either a ratio certificate (for
some pair of coordinates) or a *bounded* integral normal (`‖c‖ ≤ M`).  The normals of the
second kind are bounded vectors, so there are at most `Nat.card {c | ‖c‖ ≤ M}` of them; since a
bounded normal determines its hyperplane (as its kernel), and the hyperplanes of a chain are
pairwise distinct, at most that many elements of the family can fail to carry a certificate. -/

/-- **Discarding the bounded-height hyperplanes.**  From a family of pairwise distinct
hyperplanes, each satisfying the height dichotomy, extract the subfamily carrying a ratio
certificate; at most `Nat.card {c : Fin (n+1) → ℤ | ‖c‖ ≤ M}` elements are lost. -/
theorem exists_certified_subfamily {n : ℕ}
    (L : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (γ : Fin (n+1) → ℝ) (θ M : ℝ)
    {ι : Type*} [Fintype ι] (s : Finset ι) (Q : ι → ℝ) (b : ι → Fin (n+1) → ℤ)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → approxSpace L γ (Q i) ≠ approxSpace L γ (Q j))
    (hdich : ∀ i ∈ s, (∃ a j, a ≠ j ∧ b i a ≠ 0 ∧
        θ * Real.log (Q i) ≤ Height.logHeight₁ (((b i j : ℤ) : ℚ) / ((b i a : ℤ) : ℚ)))
      ∨ (∃ c : Fin (n+1) → ℤ, c ≠ 0 ∧ ‖c‖ ≤ M ∧
          ∀ x : Fin (n+1) → ℚ, x ∈ approxSpace L γ (Q i) ↔ ∑ j, (c j : ℚ) * x j = 0)) :
    ∃ t : Finset ι, t ⊆ s ∧
      (∀ i ∈ t, ∃ a j, a ≠ j ∧ b i a ≠ 0 ∧
        θ * Real.log (Q i) ≤ Height.logHeight₁ (((b i j : ℤ) : ℚ) / ((b i a : ℤ) : ℚ))) ∧
      s.card ≤ t.card + Nat.card {c : Fin (n+1) → ℤ // ‖c‖ ≤ M} := by
  classical
  let P : ι → Prop := fun i => ∃ a j, a ≠ j ∧ b i a ≠ 0 ∧
      θ * Real.log (Q i) ≤ Height.logHeight₁ (((b i j : ℤ) : ℚ) / ((b i a : ℤ) : ℚ))
  refine ⟨s.filter P, Finset.filter_subset _ _, fun i hi => (Finset.mem_filter.mp hi).2, ?_⟩
  set bad : Finset ι := s.filter (fun i => ¬ P i) with hbad
  have hbadsub : bad ⊆ s := Finset.filter_subset _ _
  have hch : ∀ i : ι, i ∈ bad → ∃ c : Fin (n+1) → ℤ, c ≠ 0 ∧ ‖c‖ ≤ M ∧
      ∀ x : Fin (n+1) → ℚ, x ∈ approxSpace L γ (Q i) ↔ ∑ j, (c j : ℚ) * x j = 0 := by
    intro i hi
    have hs : i ∈ s := hbadsub hi
    rcases hdich i hs with h | h
    · exact absurd h (Finset.mem_filter.mp hi).2
    · exact h
  let χ : ι → (Fin (n+1) → ℤ) := fun i => if h : i ∈ bad then Classical.choose (hch i h) else 0
  have hχ : ∀ i ∈ bad, χ i ≠ 0 ∧ ‖χ i‖ ≤ M ∧
      ∀ x : Fin (n+1) → ℚ, x ∈ approxSpace L γ (Q i) ↔ ∑ j, (χ i j : ℚ) * x j = 0 := by
    intro i hi
    rw [show χ i = Classical.choose (hch i hi) from dif_pos hi]
    exact Classical.choose_spec (hch i hi)
  have hinj : Set.InjOn χ (↑bad) := by
    intro i hi j hj hij
    by_contra hne
    refine hdist i (hbadsub hi) j (hbadsub hj) hne ?_
    ext x
    rw [(hχ i hi).2.2 x, (hχ j hj).2.2 x, hij]
  have hcard : bad.card ≤ Nat.card {c : Fin (n+1) → ℤ // ‖c‖ ≤ M} := by
    have hSfin : ({c : Fin (n+1) → ℤ | ‖c‖ ≤ M}).Finite :=
      Commons.Analysis.Normed.finite_bounded_int_vectors M
    haveI : Fintype {c : Fin (n+1) → ℤ // ‖c‖ ≤ M} := hSfin.fintype
    have hinj' : Function.Injective (fun i : ↥bad =>
        (⟨χ (i : ι), (hχ i i.2).2.1⟩ : {c : Fin (n+1) → ℤ // ‖c‖ ≤ M})) := by
      intro i j hij
      have h1 : χ (i : ι) = χ (j : ι) := Subtype.ext_iff.mp hij
      exact Subtype.ext (hinj i.2 j.2 h1)
    have h1 := Nat.card_le_card_of_injective _ hinj'
    have h2 : Nat.card ↥bad = bad.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    rwa [h2] at h1
  have hsplit : (s.filter P).card + bad.card = s.card := Finset.card_filter_add_card_filter_not P
  omega

/-- **Family reduction.**  From a finite family of pairwise distinct hyperplanes, each
satisfying the height dichotomy, extract a subfamily on which a *fixed* chart `(0,1)` works:

`s.card ≤ (n+1)^2 * t.card + Nat.card {c : Fin (n+1) → ℤ | ‖c‖ ≤ M}`,

so the loss is the pigeonhole factor `(n+1)^2` times the discarded bounded-height hyperplanes. -/
theorem family_reduction {n : ℕ} (hn : 1 ≤ n)
    (L : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (γ : Fin (n+1) → ℝ) (θ M : ℝ)
    {ι : Type*} [Fintype ι] (s : Finset ι) (Q : ι → ℝ) (b : ι → Fin (n+1) → ℤ)
    (hb : ∀ i ∈ s, b i ≠ 0)
    (hker : ∀ i ∈ s, ∀ x : Fin (n+1) → ℚ,
      x ∈ approxSpace L γ (Q i) ↔ ∑ j, (b i j : ℚ) * x j = 0)
    (hfr : ∀ i ∈ s, Module.finrank ℚ (approxSpace L γ (Q i)) = n)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → approxSpace L γ (Q i) ≠ approxSpace L γ (Q j))
    (hdich : ∀ i ∈ s, (∃ a j, a ≠ j ∧ b i a ≠ 0 ∧
        θ * Real.log (Q i) ≤ Height.logHeight₁ (((b i j : ℤ) : ℚ) / ((b i a : ℤ) : ℚ)))
      ∨ (∃ c : Fin (n+1) → ℤ, c ≠ 0 ∧ ‖c‖ ≤ M ∧
          ∀ x : Fin (n+1) → ℚ, x ∈ approxSpace L γ (Q i) ↔ ∑ j, (c j : ℚ) * x j = 0)) :
    ∃ (τ : Fin (n+1) ≃ Fin (n+1)) (t : Finset ι), t ⊆ s ∧
      s.card ≤ (n+1)^2 * t.card + Nat.card {c : Fin (n+1) → ℤ // ‖c‖ ≤ M} ∧
      ∀ i ∈ t, (b i ∘ τ) ≠ 0 ∧ (b i ∘ τ) 0 ≠ 0 ∧
        (∀ x : Fin (n+1) → ℚ,
          x ∈ approxSpace (reindexMatrix L τ) γ (Q i) ↔
            ∑ j, (((b i ∘ τ) j : ℤ) : ℚ) * x j = 0) ∧
        Module.finrank ℚ (approxSpace (reindexMatrix L τ) γ (Q i)) = n ∧
        θ * Real.log (Q i) ≤
          Height.logHeight₁ (-(((b i ∘ τ) 1 : ℤ) : ℚ) / (((b i ∘ τ) 0 : ℤ) : ℚ)) := by
  classical
  obtain ⟨s₁, hs₁, hcert, hcard₁⟩ := exists_certified_subfamily L γ θ M s Q b hdist hdich
  obtain ⟨τ, t, ht, hcard₂, hchart⟩ := pair_reduction hn L γ θ s₁ Q b
    (fun i hi => hb i (hs₁ hi)) (fun i hi => hker i (hs₁ hi)) (fun i hi => hfr i (hs₁ hi)) hcert
  refine ⟨τ, t, fun x hx => hs₁ (ht hx), ?_, hchart⟩
  omega

end Submission.Subspace
