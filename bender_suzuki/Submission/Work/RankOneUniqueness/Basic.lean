import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness.Basic` — vocabulary for the rank-one uniqueness lemma

Peterfalvi II, Ch. VII §1 (Lemma p. 268): a finite group acting faithfully and
2-transitively with a *split BN-pair of rank one* is determined up to isomorphism by the
data of `H = Q ⋊ D` and of the map `f : Q# → Q#` defined by `t x t = g(x) h(x) t f(x)`.

This module fixes the conventions:

* `Ω = G ⧸ H` is the set of left cosets with the left action `g • xH = gxH`;
* `pt H = ∞ = H` is the base point (the coset of `1`), fixed exactly by `H`;
* for `x ∈ Q`, `qPt H t x = x t H = x • (t • ∞)` is the point attached to `x`; the points
  other than `∞` are exactly the `qPt H t x`, `x ∈ Q`;
* `FRel H t x y` is the relation `∃ m ∈ H, t x t = m t y` (the book's "`f(x) = y`");
* `IsCanon H Q t g a q` says `g = a t q` with `a ∈ H`, `q ∈ Q`, the canonical form of
  `g ∉ H` (the decomposition `G ∖ H = H·t·Q` is unique);
* `FaithfulCosets H` is the faithfulness hypothesis of the lemma.

Everything here concerns groups in `Type`; finiteness is not needed for the geometric
lemmas (the book's cardinality arguments are replaced by the orbit–stabiliser bijections).
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.RankOneUniqueness

variable {G : Type*} [Group G]

/-- The base point `∞ = H` of `Ω = G ⧸ H`. -/
def pt (H : Subgroup G) : G ⧸ H := ((1 : G) : G ⧸ H)

/-- The point of `Ω = G ⧸ H` attached to `x` with respect to `t`: the coset `x t H`, which
is `x • (t • ∞)`.  For `x ∈ Q` these are exactly the points different from `∞`. -/
def qPt (H : Subgroup G) (t x : G) : G ⧸ H := ((x * t : G) : G ⧸ H)

/-- Peterfalvi's `f`-relation (II, Ch. VII §1): `t x t = m t y` for some `m ∈ H`.  For
`x ∈ Q#` this holds for exactly one `y ∈ Q#`, the book's `f(x)`. -/
def FRel (H : Subgroup G) (t x y : G) : Prop := ∃ m ∈ H, t * x * t = m * t * y

/-- The canonical form `g = a * t * q` of an element `g ∉ H` with `a ∈ H`, `q ∈ Q`. -/
def IsCanon (H Q : Subgroup G) (t g a q : G) : Prop := a ∈ H ∧ q ∈ Q ∧ g = a * t * q

/-- The action of `G` on `Ω = G ⧸ H` is faithful (hypothesis of the lemma). -/
def FaithfulCosets (H : Subgroup G) : Prop := ∀ g : G, (∀ ω : G ⧸ H, g • ω = ω) → g = 1

section Basic

variable (H : Subgroup G)

@[simp] lemma pt_def : pt H = ((1 : G) : G ⧸ H) := rfl

@[simp] lemma qPt_def (t x : G) : qPt H t x = ((x * t : G) : G ⧸ H) := rfl

/-- The action of `G` on its left cosets modulo `H`, on representatives. -/
@[simp] lemma smul_mk (a g : G) : a • (g : G ⧸ H) = ((a * g : G) : G ⧸ H) := by
  rw [MulAction.Quotient.smul_coe H a g, smul_eq_mul]

@[simp] lemma smul_pt (g : G) : g • pt H = (g : G ⧸ H) := by
  rw [pt_def, smul_mk, mul_one]

lemma mk_eq_pt_iff (g : G) : (g : G ⧸ H) = pt H ↔ g ∈ H := by
  rw [pt_def, QuotientGroup.eq]
  simp

lemma smul_pt_iff (g : G) : g • pt H = pt H ↔ g ∈ H := by
  rw [smul_pt, mk_eq_pt_iff]

lemma smul_pt_of_mem {g : G} (hg : g ∈ H) : g • pt H = pt H := (smul_pt_iff H g).mpr hg

lemma mem_of_smul_pt {g : G} (hg : g • pt H = pt H) : g ∈ H := (smul_pt_iff H g).mp hg

lemma qPt_eq_smul (t x : G) : qPt H t x = x • (t • pt H) := by
  rw [qPt_def, smul_pt, smul_mk]

end Basic

section Split

variable {H Q : Subgroup G} {t : G}

/-- `t` is an involution in the split rank-one situation. -/
lemma mul_self_eq_one (h : IsSplitRankOne H Q t) : t * t = 1 := by
  have h2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [h.invol] at this
  simpa [pow_two] using h2

lemma inv_eq_self (h : IsSplitRankOne H Q t) : t⁻¹ = t := by
  have h2 := mul_self_eq_one h
  calc t⁻¹ = (t * t) * t⁻¹ := by rw [h2, one_mul]
    _ = t := by rw [mul_assoc, mul_inv_cancel, mul_one]

/-- Multiplying by the involution `t` on both sides (twice on the left). -/
lemma mul_self_mul (h : IsSplitRankOne H Q t) (x : G) : t * (t * x) = x := by
  rw [← mul_assoc, mul_self_eq_one h, one_mul]

/-- Conjugating `e` by the involution `t` on both sides. -/
lemma involution_conj {e : G} (h2 : t * t = 1) : t * (t * e * t⁻¹) * t = e := by
  have hi : t⁻¹ = t := by
    calc t⁻¹ = (t * t) * t⁻¹ := by rw [h2, one_mul]
      _ = t := by rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [hi]
  simp only [mul_assoc]
  rw [h2, mul_one, ← mul_assoc, h2, one_mul]

lemma twoPoint_le_left (H : Subgroup G) (t : G) : twoPoint H t ≤ H := inf_le_left

lemma mem_twoPoint_iff {H : Subgroup G} {t d : G} :
    d ∈ twoPoint H t ↔ d ∈ H ∧ d ∈ conj t H := Subgroup.mem_inf

lemma mem_conj_iff (H : Subgroup G) (t d : G) :
    d ∈ conj t H ↔ ∃ e ∈ H, t * e * t⁻¹ = d := by
  rw [conj, Subgroup.mem_map]
  refine exists_congr fun e => and_congr_right fun _ => ?_
  show (MulAut.conj t) e = d ↔ t * e * t⁻¹ = d
  rw [MulAut.conj_apply]

/-- `t d t ∈ H` for `d ∈ D = H ∩ H^t`: this is what lets one absorb `D` across `t`. -/
lemma t_mul_mul_t_mem_of_mem_twoPoint {H : Subgroup G} {t d : G} (h2 : t * t = 1)
    (hd : d ∈ twoPoint H t) : t * d * t ∈ H := by
  obtain ⟨e, he, rfl⟩ := (mem_conj_iff H t d).mp hd.2
  rw [involution_conj h2]
  exact he

/-- `Q` is normalized by `H`, elementwise form. -/
lemma conj_mem_of_mem (h : IsSplitRankOne H Q t) {g a : G} (hg : g ∈ H) (ha : a ∈ Q) :
    g * a * g⁻¹ ∈ Q :=
  ((Subgroup.mem_normalizer_iff.mp (h.normal hg)) a).mp ha

/-- The points `qPt H t x` for `x ∈ Q` are never the base point. -/
lemma qPt_ne_pt (h : IsSplitRankOne H Q t) {x : G} (hx : x ∈ Q) : qPt H t x ≠ pt H := by
  intro hcon
  have h1 : x * t ∈ H := (mk_eq_pt_iff H (x * t)).mp hcon
  have h2 : t ∈ H := by
    have h3 : x⁻¹ * (x * t) ∈ H := H.mul_mem (H.inv_mem (h.le hx)) h1
    rwa [inv_mul_cancel_left] at h3
  exact h.not_mem h2

lemma t_smul_pt_ne (h : IsSplitRankOne H Q t) : t • pt H ≠ pt H := by
  intro hcon
  exact h.not_mem ((smul_pt_iff H t).mp hcon)

/-- Existence of the `Q · D` factorisation of an element of `H`. -/
lemma fact_exists (h : IsSplitRankOne H Q t) {a : G} (ha : a ∈ H) :
    ∃ q ∈ Q, ∃ d ∈ twoPoint H t, a = q * d := by
  have key : ∀ x ∈ Subgroup.closure ((Q : Set G) ∪ (twoPoint H t : Set G)),
      ∃ q ∈ Q, ∃ d ∈ twoPoint H t, x = q * d := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ =>
      ∃ q ∈ Q, ∃ d ∈ twoPoint H t, x = q * d) (fun y hy => ?_) ?_
      (fun u v _ _ ihu ihv => ?_) (fun u _ ihu => ?_) hx
    · rcases hy with hy | hy
      · exact ⟨y, hy, 1, Subgroup.one_mem _, (mul_one y).symm⟩
      · exact ⟨1, Subgroup.one_mem _, y, hy, (one_mul y).symm⟩
    · exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, (mul_one 1).symm⟩
    · obtain ⟨q₁, hq₁, d₁, hd₁, rfl⟩ := ihu
      obtain ⟨q₂, hq₂, d₂, hd₂, rfl⟩ := ihv
      refine ⟨q₁ * (d₁ * q₂ * d₁⁻¹), Q.mul_mem hq₁
          (conj_mem_of_mem h (mem_twoPoint_iff.mp hd₁).1 hq₂), d₁ * d₂,
        (twoPoint H t).mul_mem hd₁ hd₂, ?_⟩
      group
    · obtain ⟨q₁, hq₁, d₁, hd₁, rfl⟩ := ihu
      refine ⟨d₁⁻¹ * q₁⁻¹ * (d₁⁻¹)⁻¹, conj_mem_of_mem h
        (H.inv_mem (mem_twoPoint_iff.mp hd₁).1) (Q.inv_mem hq₁), d₁⁻¹,
        (twoPoint H t).inv_mem hd₁, ?_⟩
      group
  exact key a (by rw [← Subgroup.sup_eq_closure, h.sup_eq]; exact ha)

/-- Uniqueness of the `Q · D` factorisation (from `Q ∩ D = 1`). -/
lemma fact_unique (h : IsSplitRankOne H Q t) {q q' d d' : G} (hq : q ∈ Q) (hq' : q' ∈ Q)
    (hd : d ∈ twoPoint H t) (hd' : d' ∈ twoPoint H t) (heq : q * d = q' * d') :
    q = q' ∧ d = d' := by
  have h1 : q'⁻¹ * q = d' * d⁻¹ := by
    calc q'⁻¹ * q = q'⁻¹ * (q * d) * d⁻¹ := by group
      _ = q'⁻¹ * (q' * d') * d⁻¹ := by rw [heq]
      _ = d' * d⁻¹ := by group
  have hmem : q'⁻¹ * q ∈ Q ⊓ twoPoint H t :=
    ⟨Q.mul_mem (Q.inv_mem hq') hq,
      h1 ▸ (twoPoint H t).mul_mem hd' ((twoPoint H t).inv_mem hd)⟩
  have hbot : q'⁻¹ * q ∈ (⊥ : Subgroup G) := by rwa [h.inf_eq] at hmem
  have hone : q'⁻¹ * q = 1 := Subgroup.mem_bot.mp hbot
  have hqq : q' = q := inv_mul_eq_one.mp hone
  have hdd : d = d' := by
    rw [hqq] at heq
    exact mul_left_cancel heq
  exact ⟨hqq.symm, hdd⟩

end Split

end Work.RankOneUniqueness
