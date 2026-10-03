import Mathlib
import Submission.Work.Peluse.Ulower.denseExtract

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe

noncomputable section

open Work.Peluse

/-!
# The density extraction at an explicit level and with an explicit constant

`denseLevelExtract` is the `t = σ + 2` instance of the peel/Markov extraction
`Work.Peluse.Ulower.denseExtract`, but with the *explicit* constant
`|symIcc L| / (2 · |symIcc (L + 2σD)|)` in place of the unspecified positive constant `c` of
`denseExtract`.  The two conclusions are otherwise the same: a dense sub-family `H` of the shift box
`∏_{i<σ} ([1,D] × [1,D])` on which the level-two box norm of the iterated `Δ'`-difference at the
enlarged support box `symIcc (L + 2σD)` is bounded below by the constant, together with the
cardinality bound `|H| ≥ c · δ · D^{2σ}`.

The proof is the same as the one of `denseExtract`, read off the internal quantities: the peel
identity gives the average bound with `η = δ|symIcc L| / |symIcc (L + 2σD)|`, and
`Work.Peluse.Ulower.denseSet_of_avg` (Markov) then extracts the dense family.
-/

lemma denseLevelExtract {σ : ℕ} (hσ : 1 ≤ σ) {D : ℕ} (hD : 1 ≤ D) {L : ℕ} {F : ℤ → ℂ}
    (hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1) (hFspan : ∀ x : ℤ, x ∉ Work.Peluse.symIcc L → F x = 0)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hbox : δ ≤ Work.Peluse.boxNormPow (σ + 2) (fun _ : Fin (σ + 2) => Work.Peluse.arithIcc 1 D)
      (Work.Peluse.symIcc L) F) :
    ∃ H : Finset (Fin σ → ℤ × ℤ),
      H ⊆ Fintype.piFinset (fun _ : Fin σ => (Work.Peluse.arithIcc 1 D).product (Work.Peluse.arithIcc 1 D)) ∧
      δ * ((Work.Peluse.symIcc L).card : ℝ) / (2 * ((Work.Peluse.symIcc (L + 2 * σ * D)).card : ℝ))
          * ((D : ℝ)) ^ (2 * σ) ≤ (H.card : ℝ) ∧
      ∀ h ∈ H, δ * ((Work.Peluse.symIcc L).card : ℝ) / (2 * ((Work.Peluse.symIcc (L + 2 * σ * D)).card : ℝ))
        ≤ Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Work.Peluse.arithIcc 1 D)
            (Work.Peluse.symIcc (L + 2 * σ * D)) (Work.Peluse.Ulower.iterDelta' σ h F) := by
  have hsuppL : SupportIn F L := fun x hx => hFspan x (by rw [mem_symIcc_iff]; omega)
  have hfin : FinSuppZ F := FinSuppZ.of_supportIn hsuppL
  have hQne : (arithIcc 1 D).Nonempty := ⟨1, by rw [mem_arithIcc_one]; omega⟩
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  -- the peel identity
  have hpeel := boxNormPow_eq_peel_two (t := σ + 2) (by omega) (arithIcc 1 D) (symIcc L) F hfin hQne
  rw [show σ + 2 - 2 = σ from by omega] at hpeel
  have hQcard : (((arithIcc 1 D).card : ℝ)) = (D : ℝ) := by
    exact_mod_cast card_arithIcc_one D
  -- the shift-tuple index set and its cardinality
  set I : Finset (Fin σ → ℤ × ℤ) :=
    Fintype.piFinset (fun _ : Fin σ => (arithIcc 1 D).product (arithIcc 1 D)) with hI
  have hIcardN : I.card = D ^ (2 * σ) := by
    rw [hI, Fintype.card_piFinset]
    have hc : ∀ _ : Fin σ, ((arithIcc 1 D).product (arithIcc 1 D)).card = D * D := by
      intro _
      rw [show (arithIcc 1 D).product (arithIcc 1 D) = (arithIcc 1 D) ×ˢ (arithIcc 1 D) from rfl,
        Finset.card_product, card_arithIcc_one]
    rw [Finset.prod_congr rfl (fun i _ => hc i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← pow_two, ← pow_mul]
  have hIcard : ((I.card : ℝ)) = (D : ℝ) ^ (2 * σ) := by
    rw [hIcardN]; push_cast; ring
  -- the average bound for the level-two box norms (rescaled so that the support box is `symIcc L`)
  have hbox' : δ ≤ ((D : ℝ)⁻¹) ^ (2 * σ) *
      ∑ H ∈ I, boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc L) (iterDelta' σ H F) := by
    have h := hbox
    rw [hpeel] at h
    rw [hQcard] at h
    exact h
  have hS'ne : (symIcc (L + 2 * σ * D)).Nonempty :=
    ⟨0, by rw [mem_symIcc_iff]; positivity⟩
  have hsum_scale : (∑ H ∈ I,
        boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc L) (iterDelta' σ H F))
      = ((symIcc (L + 2 * σ * D)).card : ℝ) / ((symIcc L).card : ℝ) *
        ∑ H ∈ I, boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * σ * D))
          (iterDelta' σ H F) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun H _ => ?_)
    exact boxNormPow_eq_mul_card 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc L)
      (symIcc (L + 2 * σ * D)) (iterDelta' σ H F) hS'ne
  have hδsum : δ * (D : ℝ) ^ (2 * σ) ≤ ∑ H ∈ I,
      boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc L) (iterDelta' σ H F) := by
    have hDpow : (0 : ℝ) < (D : ℝ) ^ (2 * σ) := by positivity
    have hID : ((D : ℝ)⁻¹) ^ (2 * σ) * (D : ℝ) ^ (2 * σ) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hDpos), one_pow]
    calc δ * (D : ℝ) ^ (2 * σ)
        ≤ ((((D : ℝ)⁻¹) ^ (2 * σ) * ∑ H ∈ I,
            boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc L) (iterDelta' σ H F))) *
          (D : ℝ) ^ (2 * σ) := mul_le_mul_of_nonneg_right hbox' hDpow.le
      _ = (((D : ℝ)⁻¹) ^ (2 * σ) * (D : ℝ) ^ (2 * σ)) *
          ∑ H ∈ I, boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc L)
            (iterDelta' σ H F) := by ring
      _ = ∑ H ∈ I, boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc L)
            (iterDelta' σ H F) := by rw [hID, one_mul]
  -- the pointwise bound at the enlarged support box
  have hX1 : ∀ H ∈ I, boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * σ * D))
      (iterDelta' σ H F) ≤ 1 := by
    intro H hH
    have hHmem := hH
    rw [hI] at hHmem
    refine boxNormPow_two_iterDelta_le_one hF1 hFspan H (fun i => ?_)
    have hi := Fintype.mem_piFinset.mp hHmem i
    have h1 : (H i).1 ∈ arithIcc 1 D := (Finset.mem_product.mp hi).1
    have h2 : (H i).2 ∈ arithIcc 1 D := (Finset.mem_product.mp hi).2
    exact ⟨abs_le_of_mem_arithIcc_one h1, abs_le_of_mem_arithIcc_one h2⟩
  -- the scale reference and its properties
  have hSpos : (0 : ℝ) < ((symIcc L).card : ℝ) := by
    rw [card_symIcc]; push_cast; positivity
  have hS'pos : (0 : ℝ) < ((symIcc (L + 2 * σ * D)).card : ℝ) := by
    rw [card_symIcc]; push_cast; positivity
  have hcardSS : ((symIcc L).card : ℝ) ≤ ((symIcc (L + 2 * σ * D)).card : ℝ) := by
    rw [card_symIcc, card_symIcc]
    push_cast
    nlinarith [Nat.zero_le σ, Nat.zero_le D]
  set η : ℝ := δ * ((symIcc L).card : ℝ) / ((symIcc (L + 2 * σ * D)).card : ℝ) with hηdef
  have hη0 : 0 < η := by rw [hηdef]; exact div_pos (mul_pos hδ0 hSpos) hS'pos
  have hη1 : η ≤ 1 := by
    rw [hηdef, div_le_iff₀ hS'pos]
    nlinarith [hδ0, hδ1, hcardSS]
  -- the average bound, rescaled to the enlarged support box
  have hηD : η * (D : ℝ) ^ (2 * σ) ≤
      ∑ H ∈ I, boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * σ * D))
        (iterDelta' σ H F) := by
    have hkey1 : δ * (D : ℝ) ^ (2 * σ) ≤ ((symIcc (L + 2 * σ * D)).card : ℝ) /
        ((symIcc L).card : ℝ) * ∑ H ∈ I,
          boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * σ * D))
            (iterDelta' σ H F) := by
      rw [← hsum_scale]
      exact hδsum
    have hkey2 : ((symIcc L).card : ℝ) / ((symIcc (L + 2 * σ * D)).card : ℝ) *
        (δ * (D : ℝ) ^ (2 * σ)) ≤ ∑ H ∈ I,
          boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * σ * D))
            (iterDelta' σ H F) := by
      calc ((symIcc L).card : ℝ) / ((symIcc (L + 2 * σ * D)).card : ℝ) *
            (δ * (D : ℝ) ^ (2 * σ))
          ≤ ((symIcc L).card : ℝ) / ((symIcc (L + 2 * σ * D)).card : ℝ) *
              (((symIcc (L + 2 * σ * D)).card : ℝ) / ((symIcc L).card : ℝ) *
                ∑ H ∈ I, boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * σ * D))
                  (iterDelta' σ H F)) :=
            mul_le_mul_of_nonneg_left hkey1 (le_of_lt (div_pos hSpos hS'pos))
        _ = ∑ H ∈ I, boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * σ * D))
              (iterDelta' σ H F) := by
            have hc : ((symIcc L).card : ℝ) / ((symIcc (L + 2 * σ * D)).card : ℝ) *
                (((symIcc (L + 2 * σ * D)).card : ℝ) / ((symIcc L).card : ℝ)) = 1 := by
              rw [div_mul_div_comm,
                mul_comm ((symIcc (L + 2 * σ * D)).card : ℝ) ((symIcc L).card : ℝ),
                div_self (ne_of_gt (mul_pos hSpos hS'pos))]
            rw [← mul_assoc, hc, one_mul]
    have hηrewrite : η * (D : ℝ) ^ (2 * σ) = ((symIcc L).card : ℝ) /
        ((symIcc (L + 2 * σ * D)).card : ℝ) * (δ * (D : ℝ) ^ (2 * σ)) := by
      rw [hηdef]; ring
    rw [hηrewrite]
    exact hkey2
  have havg : η ≤ ((I.card : ℝ))⁻¹ *
      ∑ H ∈ I, boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * σ * D))
        (iterDelta' σ H F) := by
    rw [inv_mul_eq_div, le_div_iff₀ (by rw [hIcard]; positivity), hIcard]
    exact hηD
  -- the Markov extraction
  obtain ⟨I', hI'sub, hcardI', hpt⟩ := denseSet_of_avg I
    (fun H => boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * σ * D))
      (iterDelta' σ H F)) hη0 hη1 hX1 havg
  refine ⟨I', ?_, ?_, ?_⟩
  · intro h hh
    exact hI'sub hh
  · have hval : δ * ((symIcc L).card : ℝ) / (2 * ((symIcc (L + 2 * σ * D)).card : ℝ))
        = η / 2 := by rw [hηdef]; ring
    calc δ * ((symIcc L).card : ℝ) / (2 * ((symIcc (L + 2 * σ * D)).card : ℝ))
          * (D : ℝ) ^ (2 * σ)
        = η / 2 * (I.card : ℝ) := by rw [hval, hIcard]
      _ ≤ (I'.card : ℝ) := hcardI'
  · intro h hh
    have hval : δ * ((symIcc L).card : ℝ) / (2 * ((symIcc (L + 2 * σ * D)).card : ℝ))
        = η / 2 := by rw [hηdef]; ring
    rw [hval]
    exact hpt h hh

end

end Work.Peluse.Ulower.StepLe
