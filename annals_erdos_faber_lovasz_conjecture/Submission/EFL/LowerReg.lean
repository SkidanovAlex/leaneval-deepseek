import Submission.EFL.RegReservoir
import Submission.EFL.Reservoir

/-!
# Proposition 10.3 (`obs:del_lowerreg`): robustness of lower regularity

The paper's §10 derives optimal edge-colouring results for pseudorandom graphs.
Its Proposition 10.3 states that lower regularity is robust under
1. deleting a subgraph of bounded maximum degree, and
2. passing to a slightly larger graph.

This module proves both parts in the `2`-edge-family language of this
development (`LowerRegular` of `Reservoir.lean`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## Counting edges between two vertex sets -/

/-- `edgeCount` as a `Set.ncard`, which avoids all decidability instances. -/
theorem edgeCount_eq_ncard (R : Hypergraph (Fin n)) (S T : Finset (Fin n)) :
    edgeCount R S T = {p : Fin n × Fin n | p.1 ∈ S ∧ p.2 ∈ T ∧
      ({p.1, p.2} : Set (Fin n)) ∈ R}.ncard := by
  classical
  unfold edgeCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext p
  simp only [Finset.mem_coe, Finset.mem_filter, mem_product_iff, Set.mem_setOf_eq]
  tauto

/-- `edgeCount` is subadditive in the family. -/
theorem edgeCount_union_le (A B : Hypergraph (Fin n)) (S T : Finset (Fin n)) :
    edgeCount (A ∪ B) S T ≤ edgeCount A S T + edgeCount B S T := by
  classical
  rw [edgeCount_eq_ncard, edgeCount_eq_ncard, edgeCount_eq_ncard]
  refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (Set.ncard_union_le _ _)
  intro p hp
  simp only [Set.mem_setOf_eq, Set.mem_union] at hp ⊢
  obtain ⟨hp1, hp2, hp3⟩ := hp
  rcases hp3 with hA | hB
  · exact Or.inl ⟨hp1, hp2, hA⟩
  · exact Or.inr ⟨hp1, hp2, hB⟩

/-- The number of edges between `S` and `T` is at most the sum of the degrees
over `T`. -/
theorem edgeCount_le_sum_degAt (R : Hypergraph (Fin n)) (S T : Finset (Fin n)) :
    edgeCount R S T ≤ ∑ t ∈ T, degAt R t := by
  rw [edgeCount_eq_sum_fiber]
  exact Finset.sum_le_sum (fun t _ => fibreCount_le_degAt R S t)

/-- The union of a family with its difference from a subfamily. -/
theorem union_sdiff_eq {A B : Hypergraph (Fin n)} (h : B ⊆ A) : B ∪ (A \ B) = A := by
  ext e
  constructor
  · rintro (h' | h')
    · exact h h'
    · exact h'.1
  · intro h'
    by_cases hB : e ∈ B
    · exact Or.inl hB
    · exact Or.inr ⟨h', hB⟩

/-- **Proposition 10.3.1 (`obs:del_lowerreg` (1)), robustness of lower
regularity under the deletion of a bounded-degree subgraph.**  If
`R ⊆ E(G)` is lower `(ρ,ξ,G)`-regular and `R' ⊆ R` spans a subgraph of
maximum degree at most `α v(G)`, then `R'` is lower
`(ρ, ξ+α^{1/2}, G)`-regular. -/
theorem lowerRegular_of_delete (𝓖 R R' : Hypergraph (Fin n)) {α ρ ξ : ℝ}
    (hR' : R' ⊆ R) (hlr : LowerRegular 𝓖 R ρ ξ) (hα : 0 ≤ α) (hξ : 0 ≤ ξ)
    (hdeg : ∀ v : Fin n, (degAt (R \ R') v : ℝ) ≤ α * (n : ℝ)) :
    LowerRegular 𝓖 R' ρ (ξ + Real.sqrt α) := by
  classical
  intro S T hdisj hS hT
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsq : Real.sqrt α * Real.sqrt α = α := by
    simpa [pow_two] using Real.sq_sqrt hα
  have hξS : ξ * (n : ℝ) ≤ (S.card : ℝ) := by
    have h1 : ξ ≤ ξ + Real.sqrt α := by have := Real.sqrt_nonneg α; linarith
    nlinarith [hS, hnR]
  have hξT : ξ * (n : ℝ) ≤ (T.card : ℝ) := by
    have h1 : ξ ≤ ξ + Real.sqrt α := by have := Real.sqrt_nonneg α; linarith
    nlinarith [hT, hnR]
  have hlrS := hlr S T hdisj hξS hξT
  have h1 : (edgeCount R S T : ℝ) ≤
      (edgeCount R' S T : ℝ) + (edgeCount (R \ R') S T : ℝ) := by
    have hsplit : R' ∪ (R \ R') = R := union_sdiff_eq hR'
    have h := edgeCount_union_le R' (R \ R') S T
    rw [hsplit] at h
    exact_mod_cast h
  have h2 : (edgeCount (R \ R') S T : ℝ) ≤ ∑ _t ∈ T, α * (n : ℝ) := by
    have h := edgeCount_le_sum_degAt (R \ R') S T
    have h1 : (edgeCount (R \ R') S T : ℝ) ≤ ((∑ t ∈ T, degAt (R \ R') t : ℕ) : ℝ) := by
      exact_mod_cast h
    have h2 : ((∑ t ∈ T, degAt (R \ R') t : ℕ) : ℝ) ≤ ∑ _t ∈ T, α * (n : ℝ) := by
      rw [Nat.cast_sum]
      exact Finset.sum_le_sum (fun t _ => hdeg t)
    linarith
  have h4 : (∑ _t ∈ T, α * (n : ℝ)) = (T.card : ℝ) * (α * (n : ℝ)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h5 : α * (n : ℝ) ≤ Real.sqrt α * (S.card : ℝ) := by
    have h6 : Real.sqrt α * (n : ℝ) ≤ (S.card : ℝ) := by
      have h7 : Real.sqrt α ≤ ξ + Real.sqrt α := by linarith [Real.sqrt_nonneg α]
      nlinarith [hS, hnR]
    have h8 := mul_le_mul_of_nonneg_left h6 (Real.sqrt_nonneg α)
    nlinarith [h8, hsq]
  have h9 : (T.card : ℝ) * (α * (n : ℝ)) ≤ Real.sqrt α * (S.card : ℝ) * (T.card : ℝ) := by
    have h10 := mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg (T.card : ℕ))
    have h11 : (T.card : ℝ) * (Real.sqrt α * (S.card : ℝ)) =
        Real.sqrt α * (S.card : ℝ) * (T.card : ℝ) := by ring
    linarith [h10, h11]
  have hkey : (ξ + Real.sqrt α) * (S.card : ℝ) * (T.card : ℝ) =
      ξ * (S.card : ℝ) * (T.card : ℝ) + Real.sqrt α * (S.card : ℝ) * (T.card : ℝ) := by ring
  have hgoal : ρ * (edgeCount 𝓖 S T : ℝ) - (ξ + Real.sqrt α) * (S.card : ℝ) * (T.card : ℝ) ≤
      (edgeCount R' S T : ℝ) := by linarith [hlrS, h1, h2, h4, h9, hkey]
  exact hgoal
/-- A graph is lower `(ρ,ξ)`-regular on the vertex set `X`. -/
def SelfLowerRegular (𝓖 : Hypergraph (Fin n)) (X : Set (Fin n)) (ρ ξ : ℝ) : Prop :=
  ∀ A B : Finset (Fin n), (∀ a ∈ A, a ∈ X) → (∀ b ∈ B, b ∈ X) → Disjoint A B →
    ξ * (X.ncard : ℝ) ≤ (A.card : ℝ) → ξ * (X.ncard : ℝ) ≤ (B.card : ℝ) →
    (ρ - ξ) * (A.card : ℝ) * (B.card : ℝ) ≤ (edgeCount 𝓖 A B : ℝ)

/-- `edgeCount` is monotone in the family. -/
theorem edgeCount_mono_fam {A B : Hypergraph (Fin n)} (h : A ⊆ B) (S T : Finset (Fin n)) :
    edgeCount A S T ≤ edgeCount B S T := by
  rw [edgeCount_eq_ncard, edgeCount_eq_ncard]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro p hp
  exact ⟨hp.1, hp.2.1, h hp.2.2⟩

/-- `edgeCount` is monotone in the two vertex sets. -/
theorem edgeCount_mono_sets (R : Hypergraph (Fin n)) {A A' B B' : Finset (Fin n)}
    (hA : A' ⊆ A) (hB : B' ⊆ B) : edgeCount R A' B' ≤ edgeCount R A B := by
  rw [edgeCount_eq_ncard, edgeCount_eq_ncard]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro p hp
  exact ⟨hA hp.1, hB hp.2.1, hp.2.2⟩

/-- The final arithmetic step of Proposition 10.3.2. -/
theorem lowerReg_arith {ρ ξ α p q P Q r : ℝ} (hρξ : ξ ≤ ρ) (hα : 0 ≤ α) (hα1 : α < 1)
    (hξ0 : 0 ≤ ξ) (hP : (1 - α) * p ≤ P) (hQ : (1 - α) * q ≤ Q)
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (h1 : (ρ - ξ) * P * Q ≤ r) :
    (ρ * (1 - α) ^ 2 - ξ / (1 - α)) * p * q ≤ r := by
  have hlt : 0 < 1 - α := by linarith
  have h1m : 0 ≤ 1 - α := hlt.le
  have h1le : 1 - α ≤ 1 := by linarith
  have h0 : 0 ≤ ρ - ξ := by linarith
  have hP0 : 0 ≤ P := le_trans (mul_nonneg h1m hp0) hP
  have hsq : (1 - α) ^ 2 ≤ 1 := by nlinarith [hα, hα1, sq_nonneg α]
  have hpow : (1 - α) ^ 2 * (1 - α) ≤ 1 := by
    simpa using mul_le_mul hsq h1le h1m (by norm_num : (0:ℝ) ≤ 1)
  have hξ1 : ξ * (1 - α) ^ 2 ≤ ξ / (1 - α) := by
    rw [le_div_iff₀ hlt]
    nlinarith [hpow, hξ0]
  have hA : ρ * (1 - α) ^ 2 - ξ / (1 - α) ≤ (ρ - ξ) * (1 - α) ^ 2 := by linarith
  have hpq : 0 ≤ p * q := mul_nonneg hp0 hq0
  have hstep1 : (ρ * (1 - α) ^ 2 - ξ / (1 - α)) * (p * q) ≤
      ((ρ - ξ) * (1 - α) ^ 2) * (p * q) := mul_le_mul_of_nonneg_right hA hpq
  have hstep3 : (ρ - ξ) * ((1 - α) * p) ≤ (ρ - ξ) * P := mul_le_mul_of_nonneg_left hP h0
  have hstep4 : (ρ - ξ) * ((1 - α) * p) * ((1 - α) * q) ≤ (ρ - ξ) * P * Q :=
    mul_le_mul hstep3 hQ (mul_nonneg h1m hq0) (mul_nonneg h0 hP0)
  calc (ρ * (1 - α) ^ 2 - ξ / (1 - α)) * p * q
      = (ρ * (1 - α) ^ 2 - ξ / (1 - α)) * (p * q) := by ring
    _ ≤ ((ρ - ξ) * (1 - α) ^ 2) * (p * q) := hstep1
    _ = (ρ - ξ) * ((1 - α) * p) * ((1 - α) * q) := by ring
    _ ≤ (ρ - ξ) * P * Q := hstep4
    _ ≤ r := h1

/-- **Proposition 10.3.2 (`obs:del_lowerreg` (2)), robustness under adding
vertices.**  If `𝓖` is lower `(ρ,ξ)`-regular on `X` and `𝓗 ⊇ 𝓖` lives on a
vertex set `Y ⊇ X` with `|Y| ≤ (1+αξ)|X|`, then `𝓗` is lower
`(ρ(1-α)², ξ/(1-α))`-regular on `Y`. -/
theorem selfLowerRegular_mono (𝓖 𝓗 : Hypergraph (Fin n)) {X Y : Set (Fin n)} {α ρ ξ : ℝ}
    (hXY : X ⊆ Y) (hGX : ∀ e ∈ 𝓖, e ⊆ X) (hGH : 𝓖 ⊆ 𝓗)
    (hcard : (Y.ncard : ℝ) ≤ (1 + α * ξ) * (X.ncard : ℝ))
    (hlr : SelfLowerRegular 𝓖 X ρ ξ) (hα : 0 ≤ α) (hα1 : α < 1) (hξ : 0 < ξ) :
    SelfLowerRegular 𝓗 Y (ρ * (1 - α) ^ 2) (ξ / (1 - α)) := by
  classical
  have hlt : (0 : ℝ) < 1 - α := by linarith
  intro A B hAY hBY hdisj hA hB
  set A' : Finset (Fin n) := A.filter (fun a => a ∈ X) with hA'
  set B' : Finset (Fin n) := B.filter (fun b => b ∈ X) with hB'
  have hAsub : A' ⊆ A := Finset.filter_subset _ _
  have hBsub : B' ⊆ B := Finset.filter_subset _ _
  have hA'X : ∀ a ∈ A', a ∈ X := fun a ha => (Finset.mem_filter.mp ha).2
  have hB'X : ∀ b ∈ B', b ∈ X := fun b ha => (Finset.mem_filter.mp ha).2
  have hA'dj : Disjoint A' B' := hdisj.mono hAsub hBsub
  have hXleY : (X.ncard : ℝ) ≤ (Y.ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hXY (Set.toFinite _)
  -- `(1)` : `|Y∖X| ≤ αξ|Y|`
  have hYX : ((Y \ X).ncard : ℝ) ≤ α * ξ * (Y.ncard : ℝ) := by
    have h1 : (Y \ X).ncard = Y.ncard - X.ncard := Set.ncard_sdiff hXY (Set.toFinite _)
    have h2 : X.ncard ≤ Y.ncard := Set.ncard_le_ncard hXY (Set.toFinite _)
    have h3 : ((Y \ X).ncard : ℝ) = (Y.ncard : ℝ) - (X.ncard : ℝ) := by
      rw [h1, Nat.cast_sub h2]
    have h4 : (X.ncard : ℝ) ≤ (Y.ncard : ℝ) := by exact_mod_cast h2
    have h5 : α * ξ * (X.ncard : ℝ) ≤ α * ξ * (Y.ncard : ℝ) :=
      mul_le_mul_of_nonneg_left h4 (mul_nonneg hα hξ.le)
    rw [h3]
    nlinarith [hcard, h5]
  -- `(2)` : `A'` is `A` minus the vertices outside `X`
  have hAcard'' : (A.card : ℝ) - ((Y \ X).ncard : ℝ) ≤ (A'.card : ℝ) := by
    have hfil : A.filter (fun a => a ∉ Y \ X) = A' := by
      ext a
      rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨ha, hnot⟩
        exact ⟨ha, by by_contra hx; exact hnot ⟨hAY a ha, hx⟩⟩
      · rintro ⟨ha, hx⟩
        exact ⟨ha, fun hmem => hmem.2 hx⟩
    have hsum : (A.filter (fun a => a ∉ Y \ X)).card +
        (A.filter (fun a => a ∈ Y \ X)).card = A.card := by
      have h := Finset.card_filter_add_card_filter_not (s := A) (fun a => a ∈ Y \ X)
      rw [add_comm]
      exact h
    have hP : ((A.filter (fun a => a ∈ Y \ X)).card : ℝ) ≤ ((Y \ X).ncard : ℝ) := by
      have h3 : (A.filter (fun a => a ∈ Y \ X)).card ≤ (Y \ X).ncard := by
        rw [← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard
          (fun a ha => (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2) (Set.toFinite _)
      exact_mod_cast h3
    have hsumR : ((A.filter (fun a => a ∉ Y \ X)).card : ℝ) +
        ((A.filter (fun a => a ∈ Y \ X)).card : ℝ) = (A.card : ℝ) := by
      rw [← Nat.cast_add, hsum]
    have hfil' : ((A.filter (fun a => a ∉ Y \ X)).card : ℝ) = (A'.card : ℝ) := by
      rw [hfil]
    linarith
  have hBcard'' : (B.card : ℝ) - ((Y \ X).ncard : ℝ) ≤ (B'.card : ℝ) := by
    have hfil : B.filter (fun b => b ∉ Y \ X) = B' := by
      ext b
      rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨hb, hnot⟩
        exact ⟨hb, by by_contra hx; exact hnot ⟨hBY b hb, hx⟩⟩
      · rintro ⟨hb, hx⟩
        exact ⟨hb, fun hmem => hmem.2 hx⟩
    have hsum : (B.filter (fun b => b ∉ Y \ X)).card +
        (B.filter (fun b => b ∈ Y \ X)).card = B.card := by
      have h := Finset.card_filter_add_card_filter_not (s := B) (fun b => b ∈ Y \ X)
      rw [add_comm]
      exact h
    have hP : ((B.filter (fun b => b ∈ Y \ X)).card : ℝ) ≤ ((Y \ X).ncard : ℝ) := by
      have h3 : (B.filter (fun b => b ∈ Y \ X)).card ≤ (Y \ X).ncard := by
        rw [← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard
          (fun b hb => (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2) (Set.toFinite _)
      exact_mod_cast h3
    have hsumR : ((B.filter (fun b => b ∉ Y \ X)).card : ℝ) +
        ((B.filter (fun b => b ∈ Y \ X)).card : ℝ) = (B.card : ℝ) := by
      rw [← Nat.cast_add, hsum]
    have hfil' : ((B.filter (fun b => b ∉ Y \ X)).card : ℝ) = (B'.card : ℝ) := by
      rw [hfil]
    linarith
  -- `(3)` : `ξ|Y| ≤ (1-α)|A|`
  have hA1 : ξ * (Y.ncard : ℝ) ≤ (1 - α) * (A.card : ℝ) := by
    have h := hA
    rw [div_mul_eq_mul_div, div_le_iff₀ hlt] at h
    linarith
  have hB1 : ξ * (Y.ncard : ℝ) ≤ (1 - α) * (B.card : ℝ) := by
    have h := hB
    rw [div_mul_eq_mul_div, div_le_iff₀ hlt] at h
    linarith
  have hAn : ξ * (X.ncard : ℝ) ≤ (A'.card : ℝ) := by
    have h8 : ξ * (X.ncard : ℝ) ≤ ξ * (Y.ncard : ℝ) :=
      mul_le_mul_of_nonneg_left hXleY hξ.le
    nlinarith [hAcard'', hYX, hA1, h8, hα, hα1]
  have hBn : ξ * (X.ncard : ℝ) ≤ (B'.card : ℝ) := by
    have h8 : ξ * (X.ncard : ℝ) ≤ ξ * (Y.ncard : ℝ) :=
      mul_le_mul_of_nonneg_left hXleY hξ.le
    nlinarith [hBcard'', hYX, hB1, h8, hα, hα1]
  have hAcard : (1 - α) * (A.card : ℝ) ≤ (A'.card : ℝ) := by
    nlinarith [hAcard'', hYX, hA1, hα, hα1]
  have hBcard : (1 - α) * (B.card : ℝ) ≤ (B'.card : ℝ) := by
    nlinarith [hBcard'', hYX, hB1, hα, hα1]
  have hlrA' := hlr A' B' hA'X hB'X hA'dj hAn hBn
  have he : (edgeCount 𝓖 A' B' : ℝ) ≤ (edgeCount 𝓗 A B : ℝ) := by
    have h1 : edgeCount 𝓖 A' B' ≤ edgeCount 𝓗 A' B' := edgeCount_mono_fam hGH A' B'
    have h2 : edgeCount 𝓗 A' B' ≤ edgeCount 𝓗 A B := edgeCount_mono_sets 𝓗 hAsub hBsub
    exact_mod_cast (le_trans h1 h2)
  have hA0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
  have hA'0 : (0 : ℝ) ≤ (A'.card : ℝ) := Nat.cast_nonneg _
  have hB'0 : (0 : ℝ) ≤ (B'.card : ℝ) := Nat.cast_nonneg _
  have key : (ρ - ξ) * (A'.card : ℝ) * (B'.card : ℝ) ≤ (edgeCount 𝓗 A B : ℝ) := by
    linarith [hlrA', he]
  rcases lt_or_ge ρ ξ with hρξ | hρξ
  · have h0 : ρ * (1 - α) ^ 2 - ξ / (1 - α) ≤ 0 := by
      have h1 : ρ * (1 - α) ^ 2 ≤ ξ * (1 - α) ^ 2 :=
        mul_le_mul_of_nonneg_right hρξ.le (by positivity)
      have h2 : ξ * (1 - α) ^ 2 ≤ ξ / (1 - α) := by
        rw [le_div_iff₀ hlt]
        have h1m : 0 ≤ 1 - α := hlt.le
        have h1le : 1 - α ≤ 1 := by linarith
        have hsq : (1 - α) ^ 2 ≤ 1 := by nlinarith [hα, hα1, sq_nonneg α]
        have hpow : (1 - α) ^ 2 * (1 - α) ≤ 1 := by
          simpa using mul_le_mul hsq h1le h1m (by norm_num : (0:ℝ) ≤ 1)
        nlinarith [hpow, hξ.le]
      linarith
    have hpq : (0 : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) := mul_nonneg hA0 hB0
    have h3 : (ρ * (1 - α) ^ 2 - ξ / (1 - α)) * ((A.card : ℝ) * (B.card : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h0 hpq
    have h4 : (0 : ℝ) ≤ (edgeCount 𝓗 A B : ℝ) := Nat.cast_nonneg _
    calc (ρ * (1 - α) ^ 2 - ξ / (1 - α)) * (A.card : ℝ) * (B.card : ℝ)
        = (ρ * (1 - α) ^ 2 - ξ / (1 - α)) * ((A.card : ℝ) * (B.card : ℝ)) := by ring
      _ ≤ 0 := h3
      _ ≤ (edgeCount 𝓗 A B : ℝ) := h4
  · exact lowerReg_arith hρξ hα hα1 hξ.le hAcard hBcard hA0 hB0 key


end

end ErdosFaberLovaszConjecture
