import Mathlib
import Submission.Work.Defs.Basic

namespace Work.Geometry

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors Pointwise

/-- The set of ordered unit-distance pairs of `P` is invariant under swapping the two
coordinates, and swapping is a fixed-point-free involution on it; hence its cardinality is
even, which is exactly the statement that `cDist P = #(pairs) / 2`. -/
theorem two_mul_cDist (P : Finset ℂ) :
    2 * Work.Defs.cDist P = (P.offDiag.filter (fun pq => ‖pq.1 - pq.2‖ = 1)).card := by
  set F : Finset (ℂ × ℂ) := P.offDiag.filter (fun pq => ‖pq.1 - pq.2‖ = 1) with hF
  -- Membership characterisation of `F`.
  have memF : ∀ pq : ℂ × ℂ,
      pq ∈ F ↔ pq.1 ∈ P ∧ pq.2 ∈ P ∧ pq.1 ≠ pq.2 ∧ ‖pq.1 - pq.2‖ = 1 := by
    intro pq
    rw [hF, Finset.mem_filter, Finset.mem_offDiag]
    tauto
  -- Swapping the two coordinates preserves `F` (the norm is symmetric).
  have swap_mem : ∀ pq : ℂ × ℂ, pq ∈ F → pq.swap ∈ F := by
    rintro ⟨x, y⟩ hpq
    rw [memF] at hpq ⊢
    obtain ⟨hx, hy, hxy, hnorm⟩ := hpq
    exact ⟨hy, hx, hxy.symm, by show ‖y - x‖ = 1; rw [norm_sub_rev]; exact hnorm⟩
  -- The map sending an ordered pair to its unordered pair has fibres of size two.
  have hfib : ∀ b ∈ F.image (fun pq : ℂ × ℂ => Sym2.mk pq.1 pq.2),
      (F.filter (fun c : ℂ × ℂ => Sym2.mk c.1 c.2 = b)).card = 2 := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨⟨a₁, a₂⟩, haF, hab⟩ := hb
    have hab' : Sym2.mk a₁ a₂ = b := hab
    rw [← hab']
    obtain ⟨ha1, ha2, hane, hanorm⟩ := (memF (a₁, a₂)).mp haF
    have haF' : (a₁, a₂) ∈ F := (memF (a₁, a₂)).mpr ⟨ha1, ha2, hane, hanorm⟩
    have swap_mem' : (a₂, a₁) ∈ F := swap_mem (a₁, a₂) haF'
    have hset : F.filter (fun c : ℂ × ℂ => Sym2.mk c.1 c.2 = Sym2.mk a₁ a₂)
        = {(a₁, a₂), (a₂, a₁)} := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hmk⟩
        rcases (Sym2.mk_eq_mk_iff (p := c) (q := (a₁, a₂))).mp hmk with h | h
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h)
        · rw [h]; exact ⟨haF', rfl⟩
        · rw [h]; exact ⟨swap_mem', Sym2.eq_swap⟩
    rw [hset, Finset.card_pair_eq_two_iff]
    intro hcon
    exact hane (Prod.ext_iff.mp hcon).1
  -- Hence `#F = 2 * #(unordered pairs)`.
  have h2 : F.card = 2 * (F.image (fun pq : ℂ × ℂ => Sym2.mk pq.1 pq.2)).card := by
    calc F.card
        = ∑ b ∈ F.image (fun pq : ℂ × ℂ => Sym2.mk pq.1 pq.2),
            (F.filter (fun c : ℂ × ℂ => Sym2.mk c.1 c.2 = b)).card :=
          Finset.card_eq_sum_card_image _ _
      _ = ∑ _b ∈ F.image (fun pq : ℂ × ℂ => Sym2.mk pq.1 pq.2), 2 :=
          Finset.sum_congr rfl hfib
      _ = 2 * (F.image (fun pq : ℂ × ℂ => Sym2.mk pq.1 pq.2)).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hEven : Even F.card := by
    refine ⟨(F.image (fun pq : ℂ × ℂ => Sym2.mk pq.1 pq.2)).card, ?_⟩
    rw [h2, two_mul]
  have hc : Work.Defs.cDist P = F.card / 2 := rfl
  rw [hc]
  exact Nat.two_mul_div_two_of_even hEven

end Work.Geometry
