/-
# Ch. VII §1 (H1–H6): the identities of the canonical maps `g(x), h(x), f(x)`

Peterfalvi II, Ch. VII §1: for a split rank-one datum `H = Q ⋊ D`, `D = H ∩ H^t`, `t` an
involution outside `H`, and `x ∈ Q#`, the element `t x t` has a canonical form
`t x t = g(x) h(x) t f(x)` with `g(x), f(x) ∈ Q#`, `h(x) ∈ D`; the maps satisfy the identities
H1–H6 (loc. cit. and pp. 268–275).

Here `Work.PSU3.Canon3 H Q t x g d y` is the relation `t x t = g d t y` with `g, y ∈ Q` and
`d ∈ D`, stated for a single quadruple `(g, d, y)`, so that the identities become pure group
computations in any finite group with split rank-one data.  The proofs use only `t * t = 1`,
`Q ⊴ H`, `D = H ∩ H^t` and `Q ∩ D = 1`.

Contents (matching the lead's design `_design/PSU3Route.lean`, H1–H6):

* `canon_inv` — H1 + H4b: `f(x⁻¹) = g(x)⁻¹`, `g(x⁻¹) = f(x)⁻¹`, `h(x⁻¹) = h(x)^{-t}`;
* `canon_f` — H2 + H4c: `f(f(x)) = x` (for `x ∈ Q`), `h(f(x)) = h(x)⁻¹`;
* `canon_conj` — H3 + H4a: for `a ∈ D`, `f(x^a) = f(x)^{a^t}`, `g(x^a) = g(x)^{a^t}`,
  `h(x^a) = a^{-t} h(x) a` (with `x^a = a⁻¹ x a`);
* `canon_mul` — H6: `t (xy) t` in terms of the canonical data of `x`, `y` and of `f(x)g(y)`.
-/
import Submission.Work.PSU3.Defs
import Submission.Work.RankOneUniqueness.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness

namespace Work.PSU3

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- `D = H ∩ H^t` is stable under `d ↦ t d t`. -/
lemma tdt_mem_twoPoint {d : G} (ht : t * t = 1) (hd : d ∈ twoPoint H t) :
    t * d * t ∈ twoPoint H t := by
  have hi : t⁻¹ = t := by
    calc t⁻¹ = (t * t) * t⁻¹ := by rw [ht, one_mul]
      _ = t := by rw [mul_assoc, mul_inv_cancel, mul_one]
  refine mem_twoPoint_iff.mpr ⟨t_mul_mul_t_mem_of_mem_twoPoint ht hd, ?_⟩
  have hmem : (MulAut.conj t) d ∈ conj t H := ⟨d, (mem_twoPoint_iff.mp hd).1, rfl⟩
  simpa only [MulAut.conj_apply, hi] using hmem

/-- **H1 + H4b** (`f(x⁻¹) = g(x)⁻¹`, `g(x⁻¹) = f(x)⁻¹`, `h(x⁻¹) = h(x)^{-t}`). -/
theorem canon_inv (h : IsSplitRankOne H Q t) {x g d y : G} (hc : Canon3 H Q t x g d y) :
    Canon3 H Q t x⁻¹ y⁻¹ (t * d⁻¹ * t) g⁻¹ := by
  obtain ⟨hg, hd, hy, heq⟩ := hc
  have ht : t * t = 1 := mul_self_eq_one h
  have hi : t⁻¹ = t := inv_eq_self h
  have ht2 : ∀ a : G, t * (t * a) = a := fun a => by rw [← mul_assoc, ht, one_mul]
  refine ⟨Q.inv_mem hy, tdt_mem_twoPoint ht ((twoPoint H t).inv_mem hd), Q.inv_mem hg, ?_⟩
  have h1 : t * x⁻¹ * t = y⁻¹ * t * d⁻¹ * g⁻¹ := by
    have h2 := congrArg (fun z : G => z⁻¹) heq
    have h3 : y⁻¹ * t * d⁻¹ * g⁻¹ = t * x⁻¹ * t := by
      simpa only [mul_inv_rev, inv_inv, hi, mul_assoc] using h2.symm
    exact h3.symm
  rw [h1]
  simp only [mul_assoc, ht, ht2, mul_one]

/-- **H2 + H4c** (`f(f(x)) = x` for `x ∈ Q`, `g(f(x)) = g(x)^{h(x)}`, `h(f(x)) = h(x)⁻¹`). -/
theorem canon_f (h : IsSplitRankOne H Q t) {x g d y : G} (hx : x ∈ Q)
    (hc : Canon3 H Q t x g d y) :
    Canon3 H Q t y (d⁻¹ * g⁻¹ * d) d⁻¹ x := by
  obtain ⟨hg, hd, hy, heq⟩ := hc
  have ht : t * t = 1 := mul_self_eq_one h
  have hi : t⁻¹ = t := inv_eq_self h
  have ht2 : ∀ a : G, t * (t * a) = a := fun a => by rw [← mul_assoc, ht, one_mul]
  have hdH : d ∈ H := (mem_twoPoint_iff.mp hd).1
  refine ⟨?_, (twoPoint H t).inv_mem hd, hx, ?_⟩
  simpa only [inv_inv] using conj_mem_of_mem h (H.inv_mem hdH) (Q.inv_mem hg)
  have hy_eq : y = (g * d * t)⁻¹ * (t * x * t) := by
    have h2 := congrArg (fun z : G => (g * d * t)⁻¹ * z) heq.symm
    simpa only [inv_mul_cancel_left] using h2
  rw [hy_eq]
  simp only [mul_assoc, mul_inv_rev, inv_inv, hi, ht, ht2, one_mul, mul_one] <;> group

-- H3 + H4a (`canon_conj`), H6 (`canon_mul`) and the H6 side condition (`canon_mul_ne_one`)
-- are proved in the sibling files of this directory:
--   `Submission.Work.PSU3.RankOne.canon_conj`, `...canon_mul`, `...canon_mul_ne_one`.
-- (They are stated there exactly as in the lead's design `_design/PSU3Route.lean`.)

end Work.PSU3
