import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Arithmetic tool: if `c0` beats `M` and both `S, S'` are `≤ M`, then the value
`c0 * a + S` determines `a`. -/
private theorem sep_arith {c0 M S S' : ℕ} (hM : M < c0) (hS : S ≤ M) (hS' : S' ≤ M) :
    ∀ a b, c0 * a + S = c0 * b + S' → a = b := by
  intro a b hab
  rcases lt_trichotomy a b with h | h | h
  · have hb : a + 1 ≤ b := h
    have hlt : c0 * a + S < c0 * b + S' := by
      calc c0 * a + S ≤ c0 * a + M := Nat.add_le_add_left hS _
        _ < c0 * a + c0 := by rw [Nat.add_lt_add_iff_left]; exact hM
        _ = c0 * (a + 1) := (Nat.mul_succ c0 a).symm
        _ ≤ c0 * b := Nat.mul_le_mul_left c0 hb
        _ ≤ c0 * b + S' := Nat.le_add_right _ _
    exact absurd hab (ne_of_lt hlt)
  · exact h
  · have ha : b + 1 ≤ a := h
    have hlt : c0 * b + S' < c0 * a + S := by
      calc c0 * b + S' ≤ c0 * b + M := Nat.add_le_add_left hS' _
        _ < c0 * b + c0 := by rw [Nat.add_lt_add_iff_left]; exact hM
        _ = c0 * (b + 1) := (Nat.mul_succ c0 b).symm
        _ ≤ c0 * a := Nat.mul_le_mul_left c0 ha
        _ ≤ c0 * a + S := Nat.le_add_right _ _
    exact absurd hab.symm (ne_of_lt hlt)

/-- Separating linear weights for a finite set of functions `Fin n → ℕ`.
Proved by induction on `n`, peeling off the coordinate at `0`: the head
coordinate gets a coefficient larger than every value the tail-weight can take,
so the total weight recovers the head, and then injectivity of the tail weight
finishes. -/
theorem linWeight_inj_fun {n : ℕ} (D : Finset (Fin n → ℕ)) :
    ∃ c : Fin n → ℕ, ∀ d ∈ D, ∀ d' ∈ D,
      (∑ i, c i * d i) = (∑ i, c i * d' i) → d = d' := by
  induction n with
  | zero =>
      exact ⟨fun i => i.elim0, by intro d _ d' _ _; exact Subsingleton.elim d d'⟩
  | succ n ih =>
      let T : Finset (Fin n → ℕ) := D.image (fun d : Fin (n+1) → ℕ => fun i : Fin n => d i.succ)
      obtain ⟨c', hc'⟩ := ih T
      let S : (Fin n → ℕ) → ℕ := fun t => ∑ i, c' i * t i
      let M : ℕ := T.sup S
      refine ⟨Fin.cons (M + 1) c', ?_⟩
      intro d hd d' hd' hsum
      have hdT : (fun i : Fin n => d i.succ) ∈ T := by
        simp only [T, Finset.mem_image]; exact ⟨d, hd, rfl⟩
      have hdT' : (fun i : Fin n => d' i.succ) ∈ T := by
        simp only [T, Finset.mem_image]; exact ⟨d', hd', rfl⟩
      have hSd : S (fun i : Fin n => d i.succ) ≤ M := by
        simp only [M]; exact Finset.le_sup hdT
      have hSd' : S (fun i : Fin n => d' i.succ) ≤ M := by
        simp only [M]; exact Finset.le_sup hdT'
      have hsum' : (M + 1) * d 0 + S (fun i : Fin n => d i.succ)
          = (M + 1) * d' 0 + S (fun i : Fin n => d' i.succ) := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hsum
        simp only [Fin.cons_zero, Fin.cons_succ] at hsum
        simpa only [S] using hsum
      have h0 : d 0 = d' 0 :=
        sep_arith (Nat.lt_succ_self M) hSd hSd' (d 0) (d' 0) hsum'
      have htail : (fun i : Fin n => d i.succ) = (fun i : Fin n => d' i.succ) := by
        have hcancel : S (fun i : Fin n => d i.succ) = S (fun i : Fin n => d' i.succ) := by
          rw [h0] at hsum'
          exact Nat.add_left_cancel hsum'
        exact hc' (fun i : Fin n => d i.succ) hdT (fun i : Fin n => d' i.succ) hdT' hcancel
      have htail' : Fin.tail d = Fin.tail d' := htail
      rw [← Fin.cons_self_tail d, ← Fin.cons_self_tail d', h0, htail']

theorem linWeight_inj {n : ℕ} (D : Finset (Fin n →₀ ℕ)) :
    ∃ c : Fin n → ℕ, ∀ d ∈ D, ∀ d' ∈ D,
      (∑ i, c i * d i) = (∑ i, c i * d' i) → d = d' := by
  obtain ⟨c, hc⟩ := linWeight_inj_fun (D.image (fun d : Fin n →₀ ℕ => (⇑d : Fin n → ℕ)))
  refine ⟨c, ?_⟩
  intro d hd d' hd' hsum
  have hmem : (⇑d : Fin n → ℕ) ∈ D.image (fun d : Fin n →₀ ℕ => (⇑d : Fin n → ℕ)) :=
    Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have hmem' : (⇑d' : Fin n → ℕ) ∈ D.image (fun d : Fin n →₀ ℕ => (⇑d : Fin n → ℕ)) :=
    Finset.mem_image.mpr ⟨d', hd', rfl⟩
  have hfun : (⇑d : Fin n → ℕ) = (⇑d' : Fin n → ℕ) := hc _ hmem _ hmem' hsum
  exact Finsupp.ext (fun i => congr_fun hfun i)

end Work.BW
