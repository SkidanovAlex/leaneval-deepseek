import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.relIndex_sup_Q1_eq`

Since `Q = S × Q₁` (the two factors meet trivially and commute elementwise), passing to the
quotient by `Q₁` identifies `Q ⧸ (R ⊔ Q₁)` with `S ⧸ R` for every `R ≤ S`.  Consequently the
relative index of `R ⊔ Q₁` in `Q` equals the relative index of `R` in `S`, which is the
statement used in the two-block argument of Peterfalvi II, Appendice XII.

The proof is carried out purely with index/cardinality arithmetic:

* `card_sup_eq_card_mul_card_of_commute`: for pointwise-commuting subgroups with trivial
  intersection the cardinality of the join is the product of the cardinalities (via the
  bijection `↥A × ↥B → ↥(A ⊔ B)`, `(a, b) ↦ a * b`);
* `relIndex_mul_card_of_le`: for `H ≤ K`, `H.relIndex K * Nat.card H = Nat.card K`.

Then `|Q| / |R ⊔ Q₁| = |S| |Q₁| / (|R| |Q₁|) = |S| / |R|`.
-/

set_option linter.unusedSectionVars false

open Classical

namespace Work.FeitSibley.Coherence

noncomputable section

variable {G : Type} [Group G]

/-- If two subgroups `A`, `B` commute elementwise and meet trivially, then the cardinality of
their join is the product of their cardinalities.  (The map `↥A × ↥B → ↥(A ⊔ B)`,
`(a, b) ↦ a * b`, is a bijection.) -/
theorem card_sup_eq_card_mul_card_of_commute {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  -- every element of `A ⊔ B` is a product of an element of `A` and an element of `B`
  have hdec : ∀ {x : G}, x ∈ A ⊔ B → ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction (p := fun x _ => ∃ a ∈ A, ∃ b ∈ B, a * b = x) ?_ ?_ ?_ ?_ hx
    · rintro x (hx | hx)
      · exact ⟨x, hx, 1, B.one_mem, by rw [mul_one]⟩
      · exact ⟨1, A.one_mem, x, hx, by rw [one_mul]⟩
    · exact ⟨1, A.one_mem, 1, B.one_mem, by rw [one_mul]⟩
    · rintro x y _ _ ⟨a1, ha1, b1, hb1, hxy⟩ ⟨a2, ha2, b2, hb2, hxy2⟩
      refine ⟨a1 * a2, A.mul_mem ha1 ha2, b1 * b2, B.mul_mem hb1 hb2, ?_⟩
      rw [← hxy, ← hxy2]
      have hc : a2 * b1 = b1 * a2 := hcomm a2 ha2 b1 hb1
      calc (a1 * a2) * (b1 * b2) = a1 * a2 * b1 * b2 := by group
        _ = a1 * (a2 * b1) * b2 := by group
        _ = a1 * (b1 * a2) * b2 := by rw [hc]
        _ = a1 * b1 * a2 * b2 := by group
        _ = (a1 * b1) * (a2 * b2) := by group
    · rintro x _ ⟨a1, ha1, b1, hb1, hxy⟩
      refine ⟨a1⁻¹, A.inv_mem ha1, b1⁻¹, B.inv_mem hb1, ?_⟩
      rw [← hxy]
      have hc : a1 * b1 = b1 * a1 := hcomm a1 ha1 b1 hb1
      have hc' : b1⁻¹ * a1⁻¹ = a1⁻¹ * b1⁻¹ := by
        simpa [mul_inv_rev] using congrArg Inv.inv hc
      rw [mul_inv_rev, hc']
  let f : ↥A × ↥B → ↥(A ⊔ B) :=
    fun p => ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    simp only [f, Subtype.mk.injEq] at h
    have hmem : (a2 : G)⁻¹ * (a1 : G) = (b2 : G) * (b1 : G)⁻¹ := by
      have hh := congrArg (fun z : G => (a2 : G)⁻¹ * z * (b1 : G)⁻¹) h
      simpa [mul_assoc] using hh
    have hAB : (a2 : G)⁻¹ * (a1 : G) ∈ A ⊓ B := by
      rw [Subgroup.mem_inf]
      refine ⟨mul_mem (inv_mem a2.2) a1.2, ?_⟩
      rw [hmem]
      exact mul_mem b2.2 (inv_mem b1.2)
    rw [hinf] at hAB
    have h1 : (a2 : G)⁻¹ * (a1 : G) = 1 := Subgroup.mem_bot.mp hAB
    have haeq : a1 = a2 := by
      apply Subtype.ext
      calc (a1 : G) = (a2 : G) * ((a2 : G)⁻¹ * (a1 : G)) := by group
        _ = (a2 : G) * 1 := by rw [h1]
        _ = (a2 : G) := mul_one _
    have hbeq : b1 = b2 := by
      have h2 : (a1 : G) * (b1 : G) = (a1 : G) * (b2 : G) := by
        have h3 := h
        rw [← haeq] at h3
        exact h3
      exact Subtype.ext (mul_left_cancel h2)
    rw [haeq, hbeq]
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hdec hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  have he : ↥A × ↥B ≃ ↥(A ⊔ B) := Equiv.ofBijective f ⟨hinj, hsurj⟩
  rw [← Nat.card_congr he, Nat.card_prod]

/-- For `H ≤ K`, the relative index of `H` in `K` times the order of `H` is the order of `K`. -/
theorem relIndex_mul_card_of_le {H K : Subgroup G} (h : H ≤ K) :
    H.relIndex K * Nat.card H = Nat.card K := by
  have h1 := Subgroup.index_mul_card (H.subgroupOf K)
  rw [show (H.subgroupOf K).index = H.relIndex K from rfl] at h1
  have hc : Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  rwa [hc] at h1

theorem relIndex_sup_Q1_eq {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (R : Subgroup G) (hR : R ≤ h.S) :
    (R ⊔ h.Q1).relIndex h.Q = R.relIndex h.S := by
  -- `R` and `Q₁` commute and meet trivially, because `R ≤ S` and `S ⊓ Q₁ = ⊥`
  have hcommR : ∀ a ∈ R, ∀ b ∈ h.Q1, a * b = b * a := fun a ha b hb =>
    h.commute a (hR ha) b hb
  have hinfR : R ⊓ h.Q1 = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    obtain ⟨hxR, hxQ1⟩ := Subgroup.mem_inf.mp hx
    have hmem : x ∈ h.S ⊓ h.Q1 := Subgroup.mem_inf.mpr ⟨hR hxR, hxQ1⟩
    rw [h.S_inf_Q1] at hmem
    simpa using hmem
  -- orders of the four relevant subgroups
  have hcard_sup : Nat.card ↥(R ⊔ h.Q1) = Nat.card R * Nat.card h.Q1 :=
    card_sup_eq_card_mul_card_of_commute hcommR hinfR
  have hcard_Q : Nat.card ↥h.Q = Nat.card h.S * Nat.card h.Q1 := by
    rw [← h.S_sup_Q1]
    exact card_sup_eq_card_mul_card_of_commute (fun a ha b hb => h.commute a ha b hb) h.S_inf_Q1
  -- index arithmetic
  have hAQ : R ⊔ h.Q1 ≤ h.Q := sup_le (hR.trans h.S_le_Q) h.Q1_le_Q
  have h1 : (R ⊔ h.Q1).relIndex h.Q * Nat.card ↥(R ⊔ h.Q1) = Nat.card ↥h.Q :=
    relIndex_mul_card_of_le hAQ
  have h2 : R.relIndex h.S * Nat.card R = Nat.card h.S := relIndex_mul_card_of_le hR
  rw [hcard_sup, hcard_Q] at h1
  have hpos : 0 < Nat.card ↥h.Q1 := Nat.card_pos
  have h3 : (R ⊔ h.Q1).relIndex h.Q * Nat.card R = Nat.card h.S := by
    refine Nat.mul_right_cancel hpos ?_
    rw [mul_assoc]
    exact h1
  have hfinal : (R ⊔ h.Q1).relIndex h.Q * Nat.card R = R.relIndex h.S * Nat.card R := by
    rw [h3, h2]
  exact Nat.mul_right_cancel (Nat.card_pos (α := ↥R)) hfinal

end

end Work.FeitSibley.Coherence
