import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- Pigeonhole / union-bound lemma: if every `x ∈ Xt` satisfies `P ψ x` for at least one
`ψ ∈ Ψ`, and `Ψ` is not larger than `M`, then some single `ψ ∈ Ψ` works for a subset of
`Xt` of size at least `cA * N / M` (where `cA * N` is a lower bound for `|Xt|`). -/
theorem exists_large_fiber {α : Type*} [DecidableEq α] (P : (ℕ → ℂ) → α → Prop)
    (Xt : Finset α) (Ψ : Finset (ℕ → ℂ)) (cA N M : ℝ)
    (hcA : 0 < cA) (hN : 1 ≤ N) (hM : 0 < M) (hΨ : (Ψ.card : ℝ) ≤ M)
    (hcard : cA * N ≤ (Xt.card : ℝ))
    (hex : ∀ x ∈ Xt, ∃ ψ ∈ Ψ, P ψ x) :
    ∃ ψ ∈ Ψ, ∃ S : Finset α, S ⊆ Xt ∧ cA * N / M ≤ (S.card : ℝ) ∧ ∀ x ∈ S, P ψ x := by
  classical
  have hNpos : (0:ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hcAN : 0 < cA * N := mul_pos hcA hNpos
  have hXtcard_pos : 0 < Xt.card := by
    have h : (0:ℝ) < (Xt.card : ℝ) := lt_of_lt_of_le hcAN hcard
    exact_mod_cast h
  obtain ⟨x0, hx0⟩ := Finset.card_pos.mp hXtcard_pos
  obtain ⟨ψ1, hψ1, _⟩ := hex x0 hx0
  have hΨne : Ψ.Nonempty := ⟨ψ1, hψ1⟩
  obtain ⟨ψ₀, hψ₀, hmax⟩ :=
    Finset.exists_max_image Ψ (fun ψ => (Xt.filter (fun x => P ψ x)).card) hΨne
  have hsub : Xt ⊆ Ψ.biUnion (fun ψ => Xt.filter (fun x => P ψ x)) := by
    intro x hx
    obtain ⟨ψ, hψ, hP⟩ := hex x hx
    exact Finset.mem_biUnion.mpr ⟨ψ, hψ, Finset.mem_filter.mpr ⟨hx, hP⟩⟩
  have hcard_le_nat : Xt.card ≤ ∑ ψ ∈ Ψ, (Xt.filter (fun x => P ψ x)).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have hcard_le : (Xt.card : ℝ) ≤ ∑ ψ ∈ Ψ, ((Xt.filter (fun x => P ψ x)).card : ℝ) := by
    exact_mod_cast hcard_le_nat
  have hsum_le : (∑ ψ ∈ Ψ, ((Xt.filter (fun x => P ψ x)).card : ℝ)) ≤
      (Ψ.card : ℝ) * ((Xt.filter (fun x => P ψ₀ x)).card : ℝ) := by
    have h1 : (∑ ψ ∈ Ψ, ((Xt.filter (fun x => P ψ x)).card : ℝ)) ≤
        ∑ _ψ ∈ Ψ, (((Xt.filter (fun x => P ψ₀ x)).card : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro ψ hψ
      exact_mod_cast hmax ψ hψ
    rwa [Finset.sum_const, nsmul_eq_mul] at h1
  have hmain : cA * N ≤ M * ((Xt.filter (fun x => P ψ₀ x)).card : ℝ) := by
    have h1 : cA * N ≤ (Ψ.card : ℝ) * ((Xt.filter (fun x => P ψ₀ x)).card : ℝ) :=
      le_trans hcard (le_trans hcard_le hsum_le)
    have h2 : (Ψ.card : ℝ) * ((Xt.filter (fun x => P ψ₀ x)).card : ℝ) ≤
        M * ((Xt.filter (fun x => P ψ₀ x)).card : ℝ) :=
      mul_le_mul_of_nonneg_right hΨ (Nat.cast_nonneg _)
    linarith
  refine ⟨ψ₀, hψ₀, Xt.filter (fun x => P ψ₀ x), Finset.filter_subset _ _, ?_, ?_⟩
  · have : cA * N / M ≤ ((Xt.filter (fun x => P ψ₀ x)).card : ℝ) := by
      rw [div_le_iff₀ hM]
      linarith
    exact this
  · intro x hx
    exact (Finset.mem_filter.mp hx).2

end Work.N8
