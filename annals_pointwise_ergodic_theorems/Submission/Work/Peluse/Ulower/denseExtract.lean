import Mathlib
import Submission.Work.Peluse.Ulower.boxNormPow_eq_peel_two
import Submission.Work.Peluse.Ulower.stepBasic

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-! ## Elementary supporting lemmas

* `abs_le_of_mem_arithIcc_one`: the arithmetic-progression shift set `arithIcc 1 D = 1[1,D]`
  read as the integer interval `[1,D]` (via `Work.Peluse.Ulower.mem_arithIcc_one`);
* `norm_iterDelta'_le_one`: an iterated `Δ'`-difference of a `1`-bounded function is `1`-bounded;
* `boxNormPow_two_iterDelta_le_one`: the level-two box norm of such a difference, taken over the
  enlarged support box `symIcc (L + 2kD)`, is at most `1` (combining the pointwise bound with the
  support statement `iterDelta'_supportIn` of `stepBasic` and `boxNormPow_le_one`). -/

lemma abs_le_of_mem_arithIcc_one {D : ℕ} {a : ℤ} (h : a ∈ arithIcc 1 D) : |a| ≤ (D : ℤ) := by
  obtain ⟨h1, h2⟩ := mem_arithIcc_one.mp h
  exact abs_le.mpr ⟨by omega, h2⟩

lemma norm_iterDelta'_le_one : ∀ (k : ℕ) (sh : Fin k → ℤ × ℤ) (G : ℤ → ℂ),
    (∀ x : ℤ, ‖G x‖ ≤ 1) → ∀ x : ℤ, ‖iterDelta' k sh G x‖ ≤ 1 := by
  intro k
  induction k with
  | zero => intro sh G h x; exact h x
  | succ k ih =>
      intro sh G h x
      have hdef : iterDelta' (k + 1) sh G x =
          star (iterDelta' k (fun i => sh i.succ) G (x + (sh 0).1)) *
            iterDelta' k (fun i => sh i.succ) G (x + (sh 0).2) := rfl
      rw [hdef, norm_mul, norm_star]
      have h1 := ih (fun i => sh i.succ) G h (x + (sh 0).1)
      have h2 := ih (fun i => sh i.succ) G h (x + (sh 0).2)
      nlinarith [norm_nonneg (iterDelta' k (fun i => sh i.succ) G (x + (sh 0).1)),
        norm_nonneg (iterDelta' k (fun i => sh i.succ) G (x + (sh 0).2))]

lemma boxNormPow_two_iterDelta_le_one {k L D : ℕ} {F : ℤ → ℂ}
    (hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1) (hFs : ∀ x : ℤ, x ∉ symIcc L → F x = 0)
    (H : Fin k → ℤ × ℤ)
    (hH : ∀ i : Fin k, |(H i).1| ≤ (D : ℤ) ∧ |(H i).2| ≤ (D : ℤ)) :
    boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * k * D))
      (iterDelta' k H F) ≤ 1 := by
  have hsum : (∑ i : Fin k, ((H i).1.natAbs + (H i).2.natAbs)) ≤ 2 * k * D := by
    have hterm : ∀ i : Fin k, ((H i).1.natAbs + (H i).2.natAbs) ≤ 2 * D := by
      intro i
      have h1 : (((H i).1.natAbs : ℕ) : ℤ) ≤ (D : ℤ) := by
        rw [Int.natCast_natAbs]; exact (hH i).1
      have h2 : (((H i).2.natAbs : ℕ) : ℤ) ≤ (D : ℤ) := by
        rw [Int.natCast_natAbs]; exact (hH i).2
      omega
    calc (∑ i : Fin k, ((H i).1.natAbs + (H i).2.natAbs)) ≤ ∑ _i : Fin k, (2 * D) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = k * (2 * D) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ = 2 * k * D := by ring_nf
  have hsupport : ∀ x : ℤ, x ∉ symIcc (L + 2 * k * D) → iterDelta' k H F x = 0 := by
    intro x hx
    refine iterDelta'_supportIn k H hFs x ?_
    rw [mem_symIcc_iff] at hx ⊢
    omega
  exact Work.Peluse.BoxNorm.boxNormPow_le_one (norm_iterDelta'_le_one k H F hF1) hsupport

/-! ## The extraction of a dense family of shifts -/

theorem denseExtract {t : ℕ} (ht : 3 ≤ t) {D : ℕ} (hD : 1 ≤ D) {L : ℕ} {F : ℤ → ℂ}
    (hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1) (hFspan : ∀ x : ℤ, x ∉ Work.Peluse.symIcc L → F x = 0)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hbox : δ ≤ Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc 1 D)
      (Work.Peluse.symIcc L) F) :
    ∃ c : ℝ, 0 < c ∧ ∃ H : Finset ((Fin (t - 2) → ℤ) × (Fin (t - 2) → ℤ)),
      (∀ p ∈ H, ∀ i : Fin (t - 2),
        p.1 i ∈ Finset.Icc (1 : ℤ) (D : ℤ) ∧ p.2 i ∈ Finset.Icc (1 : ℤ) (D : ℤ)) ∧
      c * δ * (D : ℝ) ^ (2 * (t - 2)) ≤ (H.card : ℝ) ∧
      (∀ p ∈ H, c * δ ≤ Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Work.Peluse.arithIcc 1 D)
        (Work.Peluse.symIcc (L + 2 * (t - 2) * D))
        (Work.Peluse.Ulower.iterDelta' (t - 2) (fun i => (p.1 i, p.2 i)) F)) := by
  set k : ℕ := t - 2 with hk
  have ht2 : t = k + 2 := by omega
  have hsuppL : Work.Peluse.SupportIn F L := fun x hx => hFspan x (by rw [mem_symIcc_iff]; omega)
  have hfin : Work.Peluse.FinSuppZ F := Work.Peluse.FinSuppZ.of_supportIn hsuppL
  have hQne : (arithIcc 1 D).Nonempty := ⟨1, by rw [mem_arithIcc_one]; omega⟩
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < (D : ℝ) := by linarith
  -- the peel identity
  have hbox2 : δ ≤ boxNormPow (k + 2) (fun _ : Fin (k + 2) => arithIcc 1 D) (symIcc L) F := by
    rw [← ht2]
    exact hbox
  have hpeel := boxNormPow_eq_peel_two (t := k + 2) (by omega) (arithIcc 1 D) (symIcc L) F
    hfin hQne
  rw [show k + 2 - 2 = k from by omega] at hpeel
  have hQcard : (((arithIcc 1 D).card : ℝ)) = (D : ℝ) := by
    exact_mod_cast card_arithIcc_one D
  -- the shift-tuple index set and its cardinality
  set I : Finset (Fin k → ℤ × ℤ) :=
    Fintype.piFinset (fun _ : Fin k => (arithIcc 1 D).product (arithIcc 1 D)) with hI
  have hIcardN : I.card = D ^ (2 * k) := by
    rw [hI, Fintype.card_piFinset]
    have hc : ∀ _ : Fin k, ((arithIcc 1 D).product (arithIcc 1 D)).card = D * D := by
      intro _
      rw [show (arithIcc 1 D).product (arithIcc 1 D) = (arithIcc 1 D) ×ˢ (arithIcc 1 D) from rfl,
        Finset.card_product, card_arithIcc_one]
    rw [Finset.prod_congr rfl (fun i _ => hc i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← pow_two, ← pow_mul]
  have hIcard : ((I.card : ℝ)) = (D : ℝ) ^ (2 * k) := by
    rw [hIcardN]
    push_cast
    ring
  -- the average bound for the level-two box norms at the *enlarged* support box
  have hbox' : δ ≤ ((D : ℝ)⁻¹) ^ (2 * k) *
      ∑ H ∈ I, boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc L) (iterDelta' k H F) := by
    have h := hbox2
    rw [hpeel] at h
    rw [hQcard] at h
    exact h
  have hS'ne : (symIcc (L + 2 * k * D)).Nonempty :=
    ⟨0, by rw [mem_symIcc_iff]; positivity⟩
  have hsum_scale : (∑ H ∈ I,
        boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc L) (iterDelta' k H F))
      = ((symIcc (L + 2 * k * D)).card : ℝ) / ((symIcc L).card : ℝ) *
        ∑ H ∈ I, boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * k * D))
          (iterDelta' k H F) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun H _ => ?_)
    exact boxNormPow_eq_mul_card 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc L)
      (symIcc (L + 2 * k * D)) (iterDelta' k H F) hS'ne
  have hδsum : δ * (D : ℝ) ^ (2 * k) ≤ ∑ H ∈ I,
      boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc L) (iterDelta' k H F) := by
    have hDpow : (0 : ℝ) < (D : ℝ) ^ (2 * k) := by positivity
    have hID : ((D : ℝ)⁻¹) ^ (2 * k) * (D : ℝ) ^ (2 * k) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hDpos), one_pow]
    calc δ * (D : ℝ) ^ (2 * k)
        ≤ ((((D : ℝ)⁻¹) ^ (2 * k) * ∑ H ∈ I,
            boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc L) (iterDelta' k H F))) *
          (D : ℝ) ^ (2 * k) := mul_le_mul_of_nonneg_right hbox' hDpow.le
      _ = (((D : ℝ)⁻¹) ^ (2 * k) * (D : ℝ) ^ (2 * k)) *
          ∑ H ∈ I, boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc L)
            (iterDelta' k H F) := by ring
      _ = ∑ H ∈ I, boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc L)
            (iterDelta' k H F) := by rw [hID, one_mul]
  -- the pointwise bound at the enlarged box
  have hX1 : ∀ H ∈ I, boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * k * D))
      (iterDelta' k H F) ≤ 1 := by
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
  have hS'pos : (0 : ℝ) < ((symIcc (L + 2 * k * D)).card : ℝ) := by
    rw [card_symIcc]; push_cast; positivity
  have hcardSS : ((symIcc L).card : ℝ) ≤ ((symIcc (L + 2 * k * D)).card : ℝ) := by
    rw [card_symIcc, card_symIcc]
    push_cast
    nlinarith [Nat.zero_le k, Nat.zero_le D]
  set η : ℝ := δ * ((symIcc L).card : ℝ) / ((symIcc (L + 2 * k * D)).card : ℝ) with hηdef
  have hη0 : 0 < η := by rw [hηdef]; exact div_pos (mul_pos hδ0 hSpos) hS'pos
  have hη1 : η ≤ 1 := by
    rw [hηdef, div_le_iff₀ hS'pos]
    nlinarith [hδ0, hδ1, hcardSS]
  -- the average bound, rescaled
  have hηD : η * (D : ℝ) ^ (2 * k) ≤
      ∑ H ∈ I, boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * k * D))
        (iterDelta' k H F) := by
    have hkey1 : δ * (D : ℝ) ^ (2 * k) ≤ ((symIcc (L + 2 * k * D)).card : ℝ) /
        ((symIcc L).card : ℝ) * ∑ H ∈ I,
          boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * k * D))
            (iterDelta' k H F) := by
      rw [← hsum_scale]
      exact hδsum
    have hkey2 : ((symIcc L).card : ℝ) / ((symIcc (L + 2 * k * D)).card : ℝ) *
        (δ * (D : ℝ) ^ (2 * k)) ≤ ∑ H ∈ I,
          boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * k * D))
            (iterDelta' k H F) := by
      calc ((symIcc L).card : ℝ) / ((symIcc (L + 2 * k * D)).card : ℝ) *
            (δ * (D : ℝ) ^ (2 * k))
          ≤ ((symIcc L).card : ℝ) / ((symIcc (L + 2 * k * D)).card : ℝ) *
              (((symIcc (L + 2 * k * D)).card : ℝ) / ((symIcc L).card : ℝ) *
                ∑ H ∈ I, boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * k * D))
                  (iterDelta' k H F)) :=
            mul_le_mul_of_nonneg_left hkey1 (le_of_lt (div_pos hSpos hS'pos))
        _ = ∑ H ∈ I, boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * k * D))
              (iterDelta' k H F) := by
            have hc : ((symIcc L).card : ℝ) / ((symIcc (L + 2 * k * D)).card : ℝ) *
                (((symIcc (L + 2 * k * D)).card : ℝ) / ((symIcc L).card : ℝ)) = 1 := by
              rw [div_mul_div_comm,
                mul_comm ((symIcc (L + 2 * k * D)).card : ℝ) ((symIcc L).card : ℝ),
                div_self (ne_of_gt (mul_pos hSpos hS'pos))]
            rw [← mul_assoc, hc, one_mul]
    have hηrewrite : η * (D : ℝ) ^ (2 * k) = ((symIcc L).card : ℝ) /
        ((symIcc (L + 2 * k * D)).card : ℝ) * (δ * (D : ℝ) ^ (2 * k)) := by
      rw [hηdef]; ring
    rw [hηrewrite]
    exact hkey2
  have havg : η ≤ ((I.card : ℝ))⁻¹ *
      ∑ H ∈ I, boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * k * D))
        (iterDelta' k H F) := by
    rw [inv_mul_eq_div, le_div_iff₀ (by rw [hIcard]; positivity), hIcard]
    exact hηD
  -- the Markov extraction
  obtain ⟨I', hI'sub, hcardI', hpt⟩ := denseSet_of_avg I
    (fun H => boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L + 2 * k * D))
      (iterDelta' k H F)) hη0 hη1 hX1 havg
  -- repackage the function-tuples as pairs of tuples
  let Ψ : (Fin k → ℤ × ℤ) → ((Fin k → ℤ) × (Fin k → ℤ)) :=
    fun q => (fun i => (q i).1, fun i => (q i).2)
  have hΨinj : Function.Injective Ψ := by
    intro q₁ q₂ h
    funext i
    have h1 : (q₁ i).1 = (q₂ i).1 := by
      have := congrArg (fun p : (Fin k → ℤ) × (Fin k → ℤ) => p.1 i) h
      simpa [Ψ] using this
    have h2 : (q₁ i).2 = (q₂ i).2 := by
      have := congrArg (fun p : (Fin k → ℤ) × (Fin k → ℤ) => p.2 i) h
      simpa [Ψ] using this
    exact Prod.ext h1 h2
  have hcδ : ((symIcc L).card : ℝ) / (2 * ((symIcc (L + 2 * k * D)).card : ℝ)) * δ = η / 2 := by
    rw [hηdef]; ring
  refine ⟨((symIcc L).card : ℝ) / (2 * ((symIcc (L + 2 * k * D)).card : ℝ)),
    div_pos hSpos (mul_pos (by norm_num) hS'pos), ?_⟩
  refine ⟨I'.image Ψ, ?_, ?_, ?_⟩
  · intro p hp i
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp
    have hqI : q ∈ I := hI'sub hq
    rw [hI] at hqI
    have hi := Fintype.mem_piFinset.mp hqI i
    have hm1 : (q i).1 ∈ arithIcc 1 D := (Finset.mem_product.mp hi).1
    have hm2 : (q i).2 ∈ arithIcc 1 D := (Finset.mem_product.mp hi).2
    have e1 : p.1 i = (q i).1 := by rw [← hqp]
    have e2 : p.2 i = (q i).2 := by rw [← hqp]
    exact ⟨by rw [e1]; exact Finset.mem_Icc.mpr (mem_arithIcc_one.mp hm1),
      by rw [e2]; exact Finset.mem_Icc.mpr (mem_arithIcc_one.mp hm2)⟩
  · rw [Finset.card_image_of_injective _ hΨinj, hcδ, ← hIcard]
    exact hcardI'
  · intro p hp
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp
    rw [hcδ]
    have hfun : (fun i => (p.1 i, p.2 i)) = q := by
      funext i
      rw [← hqp]
    simpa only [hfun] using hpt q hq

end

end Work.Peluse.Ulower
