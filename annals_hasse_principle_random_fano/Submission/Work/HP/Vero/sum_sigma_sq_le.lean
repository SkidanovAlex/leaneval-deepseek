import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero.SigmaDefs

namespace Work.HP.Vero

/-!
# The `ℓ²` bound on the quadratic-form coefficients `σ`

For `u v : Fin (n+1) → ℤ` the vector `sigma n u v : Mon 2 n → ℤ` is the coefficient vector of the
quadratic form `t ↦ ⟨t,u⟩⟨t,v⟩`.  This file proves

`∑_m (σ(u,v)_m)² ≤ 2 · ‖u‖² · ‖v‖²`,

which is the standard `ℓ¹`/`ℓ²` comparison showing that `σ` is a bounded bilinear map into the
coefficient space.

## Proof idea

The map `(i,j) ↦ pairMon n i j` is (as we show) injective on unordered pairs: `XᵢXⱼ = X_kX_l`
iff `{i,j} = {k,l}`.  Hence every fibre of this map over `Mon 2 n` has at most two elements
`(i,j)` and `(j,i)`.  Writing `b(i,j) = u_i v_j`, the coefficient `σ(u,v)_m` is the sum of `b`
over the fibre of `m`; Cauchy–Schwarz together with the fibre bound `≤ 2` gives
`∑_m σ_m² ≤ ∑_m 2 ∑_{p ∈ fibre m} b(p)²`, and regrouping the fibres back into all ordered pairs
yields `2 ∑_{i,j} (u_i v_j)² = 2 (∑_i u_i²)(∑_j v_j²)`.
-/

/-- The `r`-th coordinate of `pairMon n i j`, as a natural number. -/
private lemma pairMon_val_eq (n : ℕ) (i j r : Fin (n+1)) :
    ((pairMon n i j).1 r).val = (if r = i then 1 else 0) + (if r = j then 1 else 0) := by
  simp only [pairMon, Work.HP.NA.monDij]

/-- The support of the monomial `XᵢXⱼ`: its `r`-th exponent is nonzero iff `r ∈ {i,j}`. -/
private lemma pairMon_val_ne_zero (n : ℕ) (i j r : Fin (n+1)) :
    ((pairMon n i j).1 r).val ≠ 0 ↔ r = i ∨ r = j := by
  rw [pairMon_val_eq]
  by_cases hi : r = i <;> by_cases hj : r = j <;> simp [hi, hj]

/-- `XᵢXⱼ = XⱼXᵢ`. -/
private lemma pairMon_comm_aux (n : ℕ) (i j : Fin (n+1)) : pairMon n i j = pairMon n j i := by
  apply Subtype.ext
  funext k
  apply Fin.ext
  simp only [pairMon, Work.HP.NA.monDij, Fin.val_mk]
  rw [Nat.add_comm]

/-- `XᵢXⱼ = X_kX_l` iff `{i,j} = {k,l}`: `pairMon` is injective on unordered pairs. -/
private lemma pairMon_eq_iff (n : ℕ) (i j k l : Fin (n+1)) :
    pairMon n i j = pairMon n k l ↔ (k = i ∧ l = j) ∨ (k = j ∧ l = i) := by
  constructor
  · intro h
    have hfun : (pairMon n i j).1 = (pairMon n k l).1 := congrArg Subtype.val h
    have hiff : ∀ r : Fin (n+1), (r = i ∨ r = j) ↔ (r = k ∨ r = l) := by
      intro r
      have := congrFun hfun r
      rw [← pairMon_val_ne_zero n i j r, ← pairMon_val_ne_zero n k l r, this]
    have hk : k = i ∨ k = j := (hiff k).mpr (Or.inl rfl)
    have hl : l = i ∨ l = j := (hiff l).mpr (Or.inr rfl)
    have hj : j = k ∨ j = l := (hiff j).mp (Or.inr rfl)
    have hi : i = k ∨ i = l := (hiff i).mp (Or.inl rfl)
    rcases hk with hk | hk
    · rcases hl with hl | hl
      · rw [hk, hl] at hj
        obtain hj | hj := hj <;> subst hj
        · exact Or.inr ⟨hk, hl⟩
        · exact Or.inr ⟨hk, hl⟩
      · exact Or.inl ⟨hk, hl⟩
    · rcases hl with hl | hl
      · exact Or.inr ⟨hk, hl⟩
      · rw [hk, hl] at hi
        obtain hi | hi := hi <;> subst hi
        · exact Or.inl ⟨hk, hl⟩
        · exact Or.inl ⟨hk, hl⟩
  · rintro (h | h)
    · obtain ⟨hk, hl⟩ := h; rw [hk, hl]
    · obtain ⟨hk, hl⟩ := h; rw [hk, hl]; exact pairMon_comm_aux n i j

theorem sum_sigma_sq_le {n : ℕ} (u v : Fin (n + 1) → ℤ) :
    (∑ m : Mon 2 n, ((sigma n u v m : ℤ) : ℝ) ^ 2)
      ≤ 2 * (∑ i, ((u i : ℤ) : ℝ) ^ 2) * (∑ j, ((v j : ℤ) : ℝ) ^ 2) := by
  classical
  -- The bilinear summand `b(i,j) = u_i v_j`.
  set b : Fin (n+1) × Fin (n+1) → ℝ := fun p => (u p.1 : ℝ) * (v p.2 : ℝ) with hb
  -- The fibre of the map `(i,j) ↦ XᵢXⱼ` over `m`.
  set F : Mon 2 n → Finset (Fin (n+1) × Fin (n+1)) :=
    fun m => Finset.univ.filter (fun p => pairMon n p.1 p.2 = m) with hF
  have hFmem : ∀ (m : Mon 2 n) (p : Fin (n+1) × Fin (n+1)),
      p ∈ F m ↔ pairMon n p.1 p.2 = m := by
    intro m p; rw [hF]; simp
  -- `σ(u,v)_m` is the sum of `b` over the fibre of `m`.
  have hsig : ∀ m : Mon 2 n, ((sigma n u v m : ℤ) : ℝ) = ∑ p ∈ F m, b p := by
    intro m
    rw [hb, hF, Finset.sum_filter]
    rw [sigma]
    push_cast
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases h : m = pairMon n i j
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right (fun hh => h hh.symm)]
  have hS : (∑ m : Mon 2 n, ((sigma n u v m : ℤ) : ℝ) ^ 2)
      = ∑ m, (∑ p ∈ F m, b p)^2 := by
    refine Finset.sum_congr rfl (fun m _ => ?_); rw [hsig m]
  rw [hS]
  -- Every fibre has at most two elements.
  have hcard : ∀ m : Mon 2 n, (F m).card ≤ 2 := by
    intro m
    rcases Finset.eq_empty_or_nonempty (F m) with hem | ⟨p, hp⟩
    · rw [hem]; simp
    · have hsub : F m ⊆ {p, (p.2, p.1)} := by
        intro q hq
        have hqm : pairMon n q.1 q.2 = m := (hFmem m q).mp hq
        have hpm : pairMon n p.1 p.2 = m := (hFmem m p).mp hp
        have heq : pairMon n p.1 p.2 = pairMon n q.1 q.2 := by rw [hpm, hqm]
        rcases (pairMon_eq_iff n p.1 p.2 q.1 q.2).mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inl (Prod.ext h1 h2)
        · rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr (Prod.ext h1 h2)
      calc (F m).card ≤ ({p, (p.2, p.1)} : Finset (Fin (n+1) × Fin (n+1))).card :=
            Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
  -- Cauchy–Schwarz over each fibre, using the fibre bound.
  have hstep : ∀ m : Mon 2 n, (∑ p ∈ F m, b p)^2 ≤ 2 * ∑ p ∈ F m, (b p)^2 := by
    intro m
    have h1 : (∑ p ∈ F m, b p)^2 ≤ ((F m).card : ℝ) * ∑ p ∈ F m, (b p)^2 :=
      sq_sum_le_card_mul_sum_sq
    have h2 : ((F m).card : ℝ) ≤ 2 := by exact_mod_cast hcard m
    have h3 : 0 ≤ ∑ p ∈ F m, (b p)^2 := Finset.sum_nonneg (fun p _ => sq_nonneg _)
    nlinarith [h1, h2, h3]
  have hb2 : ∑ p, (b p)^2
      = (∑ i, ((u i : ℤ) : ℝ) ^ 2) * (∑ j, ((v j : ℤ) : ℝ) ^ 2) := by
    rw [hb]
    simp only [mul_pow]
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  calc ∑ m, (∑ p ∈ F m, b p)^2
      ≤ ∑ m, 2 * ∑ p ∈ F m, (b p)^2 := Finset.sum_le_sum (fun m _ => hstep m)
    _ = 2 * ∑ m, ∑ p ∈ F m, (b p)^2 := by rw [Finset.mul_sum]
    _ = 2 * ∑ p, (b p)^2 := by
          congr 1
          simp only [hF]
          exact Finset.sum_fiberwise Finset.univ
            (fun p : Fin (n+1) × Fin (n+1) => pairMon n p.1 p.2) (fun p => (b p)^2)
    _ = 2 * (∑ i, ((u i : ℤ) : ℝ) ^ 2) * (∑ j, ((v j : ℤ) : ℝ) ^ 2) := by
          rw [hb2]; ring

end Work.HP.Vero
