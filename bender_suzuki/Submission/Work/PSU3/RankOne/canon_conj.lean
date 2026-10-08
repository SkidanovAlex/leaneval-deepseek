import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.PSU3.RankOne.H16

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness

namespace Work.PSU3.RankOne

/-- For an involution `t` (`t * t = 1`), `(t a t)⁻¹ = t a⁻¹ t`. -/
lemma tdt_inv_eq {G : Type} [Group G] {t a : G} (ht : t * t = 1) :
    (t * a * t)⁻¹ = t * a⁻¹ * t := by
  have hti : t⁻¹ = t := inv_eq_iff_mul_eq_one.mpr ht
  rw [mul_inv_rev, mul_inv_rev, hti, mul_assoc]

/-- **H4a, `d`-component.**  For `a, d ∈ D = twoPoint H t` with `t` an involution, the element
`(t a t)⁻¹ * d * a` again lies in `D`.  This is Peterfalvi's `h(x^a) = a^{-t} h(x) a`. -/
lemma tdt_inv_mul_mem_twoPoint {G : Type} [Group G] {H : Subgroup G} {t a d : G}
    (ht : t * t = 1) (ha : a ∈ twoPoint H t) (hd : d ∈ twoPoint H t) :
    (t * a * t)⁻¹ * d * a ∈ twoPoint H t := by
  have hti : t⁻¹ = t := inv_eq_iff_mul_eq_one.mpr ht
  have hts : ∀ z : G, t * (t * z) = z := fun z => by rw [← mul_assoc, ht, one_mul]
  have hAinv : (t * a * t)⁻¹ = t * a⁻¹ * t := tdt_inv_eq ht
  have haH : a ∈ H := (mem_twoPoint_iff.mp ha).1
  have hdH : d ∈ H := (mem_twoPoint_iff.mp hd).1
  refine mem_twoPoint_iff.mpr ⟨?_, ?_⟩
  · rw [hAinv]
    exact H.mul_mem (H.mul_mem
      (t_mul_mul_t_mem_of_mem_twoPoint ht ((twoPoint H t).inv_mem ha)) hdH) haH
  · have hconj : t * ((t * a⁻¹ * t) * d * a) * t = a⁻¹ * (t * d * t) * (t * a * t) := by
      simp only [mul_assoc, hts]
    rw [mem_conj_iff]
    refine ⟨t * ((t * a⁻¹ * t) * d * a) * t, hconj ▸ ?_, ?_⟩
    · exact H.mul_mem (H.mul_mem (H.inv_mem haH) (t_mul_mul_t_mem_of_mem_twoPoint ht hd))
        (t_mul_mul_t_mem_of_mem_twoPoint ht ha)
    · rw [hti, hAinv]
      simp only [mul_assoc, hts, ht, mul_one]

/-- **H3 + H4a.**  For `a ∈ D = H ∩ H^t`,
`f(x^a) = f(x)^{a^t}`, `g(x^a) = g(x)^{a^t}` and `h(x^a) = a^{-t} h(x) a`, here combined in the
single statement `t x t = g h t y → t (a⁻¹ x a) t = g' d' t y'` with
`g' = (t a t)⁻¹ g (t a t)`, `d' = (t a t)⁻¹ d a`, `y' = (t a t)⁻¹ y (t a t)`. -/
theorem canon_conj {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) {x g d y a : G}
    (ha : a ∈ Submission.Blueprint.twoPoint H t) (hc : Work.PSU3.Canon3 H Q t x g d y) :
    Work.PSU3.Canon3 H Q t (a⁻¹ * x * a) ((t * a * t)⁻¹ * g * (t * a * t))
      ((t * a * t)⁻¹ * d * a) ((t * a * t)⁻¹ * y * (t * a * t)) := by
  obtain ⟨hg, hd, hy, heq⟩ := hc
  have ht : t * t = 1 := mul_self_eq_one h
  have hts : ∀ z : G, t * (t * z) = z := fun z => by rw [← mul_assoc, ht, one_mul]
  have hAinv : (t * a * t)⁻¹ = t * a⁻¹ * t := tdt_inv_eq ht
  have hAH : t * a * t ∈ H := t_mul_mul_t_mem_of_mem_twoPoint ht ha
  have hAinvH : (t * a * t)⁻¹ ∈ H := H.inv_mem hAH
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [inv_inv] using conj_mem_of_mem h hAinvH hg
  · exact tdt_inv_mul_mem_twoPoint ht ha hd
  · simpa only [inv_inv] using conj_mem_of_mem h hAinvH hy
  · have key1 : (t * a * t)⁻¹ * (t * x * t) * (t * a * t) = t * (a⁻¹ * x * a) * t := by
      rw [hAinv]
      simp only [mul_assoc, hts]
    have key2 : ((t * a * t)⁻¹ * g * (t * a * t)) * ((t * a * t)⁻¹ * d * a) * t *
        ((t * a * t)⁻¹ * y * (t * a * t)) = (t * a * t)⁻¹ * (t * x * t) * (t * a * t) := by
      rw [heq, hAinv]
      simp only [mul_assoc, hts, mul_inv_cancel_left]
    rw [← key1, key2]

end Work.PSU3.RankOne
