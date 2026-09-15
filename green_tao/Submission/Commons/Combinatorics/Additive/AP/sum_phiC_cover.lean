import Mathlib
import Submission.Commons.Combinatorics.Additive.AP.sum_of_two_linear_forms
import Submission.Commons.Combinatorics.Additive.AP.surj_two_linear_forms

namespace Commons.Combinatorics.Additive.AP

open Finset

theorem sum_phiC_cover {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 3 ≤ k)
    (c : Fin k → ZMod p) (hc : Function.Injective c) (hc0 : c ⟨0, by omega⟩ = 0)
    (G : ZMod p → ZMod p → ℝ) :
    (∑ u : Fin (k-1) → ZMod p,
        G (∑ t, u t) (∑ t, u t * (c ⟨t.val+1, by omega⟩)⁻¹))
      = (p : ℝ)^(k-3) * ∑ q : ZMod p × ZMod p, G q.1 q.2 := by
  have hn : 2 ≤ k - 1 := by omega
  have hsub : k - 1 - 2 = k - 3 := by omega
  have h12 : c ⟨1, by omega⟩ ≠ c ⟨2, by omega⟩ := by
    intro h
    have h' : (⟨1, by omega⟩ : Fin k) = ⟨2, by omega⟩ := hc h
    have hv := congrArg Fin.val h'
    simp at hv
  have hinv : (c ⟨2, by omega⟩ : ZMod p)⁻¹ ≠ (c ⟨1, by omega⟩)⁻¹ := by
    intro h
    apply h12
    rw [← inv_inv (c ⟨2, by omega⟩), h, inv_inv]
  have hne : ∃ i j : Fin (k-1),
      (fun _ : Fin (k-1) => (1 : ZMod p)) i * (c ⟨j.val + 1, by omega⟩)⁻¹
        ≠ (fun _ : Fin (k-1) => (1 : ZMod p)) j * (c ⟨i.val + 1, by omega⟩)⁻¹ := by
    refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
    simp only [one_mul]
    simpa using hinv
  have hsurj : Function.Surjective
      (fun y : Fin (k-1) → ZMod p =>
        (∑ i, (fun _ : Fin (k-1) => (1 : ZMod p)) i * y i,
         ∑ i, (c ⟨i.val + 1, by omega⟩)⁻¹ * y i)) :=
    surj_two_linear_forms (p := p) (n := k-1) hn
      (fun _ : Fin (k-1) => (1 : ZMod p)) (fun i => (c ⟨i.val + 1, by omega⟩)⁻¹) hne
  have key := sum_of_two_linear_forms (p := p) (n := k-1) hn
      (fun _ : Fin (k-1) => (1 : ZMod p)) (fun i => (c ⟨i.val + 1, by omega⟩)⁻¹)
      hsurj (fun z : ZMod p × ZMod p => G z.1 z.2)
  rw [hsub] at key
  trans (∑ y : Fin (k-1) → ZMod p,
      G (∑ i, (1 : ZMod p) * y i) (∑ i, (c ⟨i.val + 1, by omega⟩)⁻¹ * y i))
  · apply Finset.sum_congr rfl
    intro y _
    congr 1
    · exact Finset.sum_congr rfl (fun i _ => by rw [one_mul])
    · apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm]
  · simpa using key

end Commons.Combinatorics.Additive.AP
