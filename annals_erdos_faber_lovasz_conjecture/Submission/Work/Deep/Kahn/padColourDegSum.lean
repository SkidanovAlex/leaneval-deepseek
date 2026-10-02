import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.Pad

set_option linter.style.haveILetI false

namespace Work.Deep.Kahn

open scoped BigOperators
open ErdosFaberLovaszConjecture

/-- **Sum of the colour degrees over the colour set.**  For a vertex `v` of the `C`-uniform
padding of `𝓗` and an injection `ρ` of the colour set, the sum over all colours `γ'` of the
number of padded edges through `v` whose list (an image `(L e).image ρ`) contains `γ'` equals
`Λ` times the number of padded edges through `v`.  (Both sides count the pairs `(e, γ')` with
`e ∋ v` and `γ' ∈ (L e).image ρ`, using `#((L e).image ρ) = #(L e) = Λ`.) -/
theorem padColourDegSum {n c C Λ : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {L : 𝓗 → Finset (Fin c)} (hlist : ∀ e : 𝓗, (L e).card = Λ)
    {c' : ℕ} {ρ : Fin c → Fin c'} (hρ : Function.Injective ρ) (v : Work.Deep.Kahn.PV n C 𝓗) :
    ∑ γ' : Fin c', Nat.card {e : 𝓗 // v ∈ Work.Deep.Kahn.padEdge C 𝓗 e ∧ γ' ∈ (L e).image ρ}
      = Λ * Nat.card {e : 𝓗 // v ∈ Work.Deep.Kahn.padEdge C 𝓗 e} := by
  classical
  -- `𝓗` is a set of edges over the finite vertex set `Fin n`, hence a finite type.
  haveI : Fintype ↥𝓗 := Fintype.ofFinite 𝓗
  -- Every (padded) edge has exactly `Λ` colours in its pulled-back list.
  have hL : ∀ e : 𝓗, ((L e).image ρ).card = Λ := fun e =>
    (Finset.card_image_of_injective (L e) hρ).trans (hlist e)
  -- `Nat.card` of a subtype of `↥𝓗` is the cardinality of the corresponding filtered finset.
  have hcard1 : ∀ γ' : Fin c',
      Nat.card {e : 𝓗 // v ∈ Work.Deep.Kahn.padEdge C 𝓗 e ∧ γ' ∈ (L e).image ρ}
      = ((Finset.univ.filter
          (fun e : 𝓗 => v ∈ Work.Deep.Kahn.padEdge C 𝓗 e ∧ γ' ∈ (L e).image ρ)).card : ℕ) := by
    intro γ'
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcard2 : Nat.card {e : 𝓗 // v ∈ Work.Deep.Kahn.padEdge C 𝓗 e}
      = ((Finset.univ.filter (fun e : 𝓗 => v ∈ Work.Deep.Kahn.padEdge C 𝓗 e)).card : ℕ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- `Λ` copies of the number of padded edges through `v`, written as a sum.
  have hsum : Λ * ((Finset.univ.filter
        (fun e : 𝓗 => v ∈ Work.Deep.Kahn.padEdge C 𝓗 e)).card : ℕ)
      = ∑ e ∈ (Finset.univ.filter (fun e : 𝓗 => v ∈ Work.Deep.Kahn.padEdge C 𝓗 e)), Λ := by
    rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]
  -- Double counting: rewrite every term of both sides as a sum of indicators.
  simp only [hcard1, hcard2]
  rw [hsum]
  -- `∑ γ', (univ.filter (P ∧ γ' ∈ I)).card = ∑ γ' ∑ e, [P e ∧ γ' ∈ I e]`
  simp only [Finset.card_filter]
  -- Interchange the two sums.
  rw [Finset.sum_comm]
  -- `∑ e ∑ γ', [P e ∧ γ' ∈ I e] = ∑ e, (if P e then Λ else 0)`
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  -- For a fixed edge `e`: sum the indicator of `γ' ∈ (L e).image ρ`, or `0` if `e` misses `v`.
  by_cases h : v ∈ Work.Deep.Kahn.padEdge C 𝓗 e
  · rw [if_pos h]
    simp only [h, true_and]
    have hIe : (Finset.univ.filter (fun γ' : Fin c' => γ' ∈ (L e).image ρ)) = (L e).image ρ :=
      Finset.filter_univ_mem _
    rw [← Finset.card_filter, hIe, hL e]
  · simp [h]

end Work.Deep.Kahn
