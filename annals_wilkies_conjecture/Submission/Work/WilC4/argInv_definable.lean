import Mathlib
import Submission.Work.WilC4.RatioLowerDefs
import Submission.Work.WilC4.DiagDefs

namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-- The argument-inverted family `ArgInv Y` is `∅`-definable in `LRc` as soon as `Y` is.

`ArgInv Y = {v | ∃ u : Fin 1 → ℝ, u 0 * v 0 = 1 ∧ (Sum.elim v u) ∘ ArgInvEmb ∈ Y}` is a finite
existential projection (over the single coordinate `u`) of the intersection of
* the preimage of `Y` under the (term-definable) relabelling `w ↦ w ∘ ArgInvEmb`, and
* the polynomial constraint `w (inr 0) * w (inl 0) = 1`. -/
theorem argInv_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (ArgInv Y) := by
  -- The preimage of `Y` under the relabelling `w ↦ w ∘ ArgInvEmb k`.
  have h1 : (∅ : Set ℝ).Definable LRc
      {w : (Fin (k + 2) ⊕ Fin 1) → ℝ | (w ∘ ArgInvEmb k) ∈ Y} :=
    hY.preimage_comp (ArgInvEmb k)
  -- The polynomial constraint `w (inr 0) * w (inl 0) = 1`.
  have h2 : (∅ : Set ℝ).Definable LRc
      {w : (Fin (k + 2) ⊕ Fin 1) → ℝ |
        w (Sum.inr (0 : Fin 1)) * w (Sum.inl (0 : Fin (k + 2))) = 1} := by
    rw [← definable_univ_iff_empty]
    have h := definable_eval_eq_LRc (σ := Fin (k + 2) ⊕ Fin 1)
      (MvPolynomial.X (Sum.inr (0 : Fin 1)) * MvPolynomial.X (Sum.inl (0 : Fin (k + 2)))) 1
    simpa using h
  have hbody := h1.inter h2
  -- `ArgInv Y` is exactly the finite existential projection of the body above.
  have hset : ArgInv Y = {v : Fin (k + 2) → ℝ | ∃ u : Fin 1 → ℝ,
      Sum.elim v u ∈ ({w : (Fin (k + 2) ⊕ Fin 1) → ℝ | (w ∘ ArgInvEmb k) ∈ Y} ∩
        {w : (Fin (k + 2) ⊕ Fin 1) → ℝ |
          w (Sum.inr (0 : Fin 1)) * w (Sum.inl (0 : Fin (k + 2))) = 1})} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Sum.elim_inr, Sum.elim_inl, ArgInv]
    constructor
    · rintro ⟨u, hu, hYmem⟩
      exact ⟨u, hYmem, hu⟩
    · rintro ⟨u, hYmem, hu⟩
      exact ⟨u, hu, hYmem⟩
  rw [hset]
  exact hbody.exists_of_finite

end Work.WilC4
