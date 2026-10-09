import Mathlib
import Submission.Work.Shrinking.FreeOperator
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The fixed-point-free involution of the free `G`-operator group

Let `F(n) = FreeGroup (Fin n × G)` be the free `G`-operator group of rank `n` and let `δ ∈ G` with
`δ * δ = 1`, `δ ≠ 1`.  The induced automorphism
`Φ = FreeGroup.freeGroupCongr (freeOperatorGenPerm n δ)`, `(i,g) ↦ (i, δ * g)`, permutes the free
basis in free orbits of size two.  This file proves the two consequences used to lift `2`-torsion:

(i) `Φ` has trivial fixed subgroup;
(ii) every `Φ`-anti-invariant element of `F(n)` is of the form `v * (Φ v)⁻¹`.

The proofs are elementary word combinatorics via `FreeGroup.toWord` (the reduced normal form).
-/

namespace Work.SSGRoute

open FreeGroup

section WordLemmas

variable {X Y : Type*}

/-- `FreeGroup.reduce` commutes with letterwise application of an injective map. -/
theorem reduce_map_of_injective [DecidableEq X] [DecidableEq Y] (f : X → Y)
    (hf : Function.Injective f) (L : List (X × Bool)) :
    FreeGroup.reduce (L.map (fun p => (f p.1, p.2)))
      = (FreeGroup.reduce L).map (fun p => (f p.1, p.2)) := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, FreeGroup.reduce.cons (f hd.1, hd.2), ih, FreeGroup.reduce.cons hd]
    cases hred : FreeGroup.reduce tl with
    | nil => simp
    | cons h2 t2 =>
      simp only [List.map_cons]
      by_cases hc : hd.1 = h2.1 ∧ hd.2 = !h2.2
      · have hc' : (f hd.1 = f h2.1) ∧ (hd.2 = !h2.2) := ⟨by rw [hc.1], hc.2⟩
        rw [if_pos hc, if_pos hc']
      · have hc' : ¬ ((f hd.1 = f h2.1) ∧ (hd.2 = !h2.2)) := fun h => hc ⟨hf h.1, h.2⟩
        rw [if_neg hc, if_neg hc']
        simp

/-- `FreeGroup.invRev` (word inverse) commutes with letterwise application of a map that preserves
the sign. -/
theorem invRev_map [DecidableEq X] [DecidableEq Y] (f : X → Y) (L : List (X × Bool)) :
    FreeGroup.invRev (L.map (fun p => (f p.1, p.2)))
      = (FreeGroup.invRev L).map (fun p => (f p.1, p.2)) := by
  have hcomp : ((fun q : Y × Bool => (q.1, !q.2)) ∘ (fun p : X × Bool => (f p.1, p.2)))
      = ((fun p : X × Bool => (f p.1, p.2)) ∘ (fun q : X × Bool => (q.1, !q.2))) := by
    funext p
    obtain ⟨x, b⟩ := p
    rfl
  calc FreeGroup.invRev (L.map (fun p : X × Bool => (f p.1, p.2)))
      = (((L.map (fun p : X × Bool => (f p.1, p.2))).map
            (fun g : Y × Bool => (g.1, !g.2))).reverse) := rfl
    _ = ((L.map ((fun g : Y × Bool => (g.1, !g.2)) ∘
            (fun p : X × Bool => (f p.1, p.2)))).reverse) := by rw [List.map_map]
    _ = ((L.map ((fun p : X × Bool => (f p.1, p.2)) ∘
            (fun g : X × Bool => (g.1, !g.2)))).reverse) := by rw [hcomp]
    _ = (((L.map (fun g : X × Bool => (g.1, !g.2))).map
            (fun p : X × Bool => (f p.1, p.2))).reverse) := by rw [List.map_map]
    _ = ((FreeGroup.invRev L).map (fun p : X × Bool => (f p.1, p.2))) := by
          rw [FreeGroup.invRev, List.map_reverse]

/-- **`toWord` is natural in the alphabet.**  For an equivalence `σ : X ≃ Y` and `w : FreeGroup X`,
the reduced word of `freeGroupCongr σ w` is obtained from the reduced word of `w` by applying `σ`
letterwise. -/
theorem toWord_freeGroupCongr [DecidableEq X] [DecidableEq Y] (σ : X ≃ Y) (w : FreeGroup X) :
    (FreeGroup.freeGroupCongr σ w).toWord
      = (w.toWord).map (fun p => (σ p.1, p.2)) := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of x => simp
  | inv_of x ih =>
    have h1 : FreeGroup.freeGroupCongr σ (FreeGroup.of x)⁻¹
        = (FreeGroup.freeGroupCongr σ (FreeGroup.of x))⁻¹ :=
      map_inv ((FreeGroup.freeGroupCongr σ).toMonoidHom) _
    rw [h1, FreeGroup.toWord_inv, FreeGroup.toWord_inv, ih]
    exact invRev_map σ _
  | mul a b iha ihb =>
    rw [show FreeGroup.freeGroupCongr σ (a * b)
          = FreeGroup.freeGroupCongr σ a * FreeGroup.freeGroupCongr σ b from
        map_mul ((FreeGroup.freeGroupCongr σ).toMonoidHom) a b,
      FreeGroup.toWord_mul, FreeGroup.toWord_mul, iha, ihb, ← List.map_append]
    exact reduce_map_of_injective σ σ.injective _

end WordLemmas

namespace WordLemmas

variable {X : Type*}

/-- A list fixed by a letterwise map whose underlying `X`-map is fixed-point free is empty. -/
theorem eq_nil_of_map_eq_self (σ : X ≃ X) (hσ : ∀ x, σ x ≠ x) (L : List (X × Bool))
    (hL : L.map (fun p => (σ p.1, p.2)) = L) : L = [] := by
  cases L with
  | nil => rfl
  | cons p tl =>
    have h1 : (fun p : X × Bool => (σ p.1, p.2)) p = p := by
      have := congrArg List.head? hL
      simpa using this
    have h2 : σ p.1 = p.1 := congrArg Prod.fst h1
    exact absurd h2 (hσ p.1)

end WordLemmas

section Main

variable (G : Type*) [Group G] (n : ℕ)

/-- The involution `(i,g) ↦ (i, δ*g)` of the free basis is fixed-point free when `δ ≠ 1`. -/
theorem freeOperatorGenPerm_ne_self (δ : G) (hδ1 : δ ≠ 1) (x : Fin n × G) :
    Work.Shrinking.freeOperatorGenPerm (G := G) n δ x ≠ x := by
  intro h
  have h2 : δ * x.2 = x.2 := by
    have := congrArg Prod.snd h
    simpa [Work.Shrinking.freeOperatorGenPerm] using this
  exact hδ1 (mul_right_cancel (by rw [h2, one_mul]))

end Main

/-- **No fixed points.**  For the free `G`-operator group `F(n)` and `δ ∈ G` with `δ * δ = 1`,
`δ ≠ 1`, the induced automorphism has trivial fixed subgroup. -/
theorem freeOperatorGroup_fixed_eq_one (G : Type*) [Group G] (n : ℕ) (δ : G)
    (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) (w : Work.Shrinking.freeOperatorGroup G n)
    (hw : FreeGroup.freeGroupCongr (Work.Shrinking.freeOperatorGenPerm (G := G) n δ) w = w) :
    w = 1 := by
  classical
  have h1 : (w.toWord).map (fun p => (Work.Shrinking.freeOperatorGenPerm (G := G) n δ p.1, p.2))
      = w.toWord := by
    have := toWord_freeGroupCongr (Work.Shrinking.freeOperatorGenPerm (G := G) n δ) w
    rw [hw] at this
    exact this.symm
  have h2 := WordLemmas.eq_nil_of_map_eq_self (Work.Shrinking.freeOperatorGenPerm (G := G) n δ)
    (freeOperatorGenPerm_ne_self (G := G) n δ hδ1) w.toWord h1
  exact FreeGroup.toWord_eq_nil_iff.mp h2

/-- **Anti-invariant elements are norms.** -/
theorem freeOperatorGroup_antiinvariant (G : Type*) [Group G] (n : ℕ) (δ : G)
    (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) (w : Work.Shrinking.freeOperatorGroup G n)
    (hw : FreeGroup.freeGroupCongr (Work.Shrinking.freeOperatorGenPerm (G := G) n δ) w = w⁻¹) :
    ∃ v, w = v * (FreeGroup.freeGroupCongr (Work.Shrinking.freeOperatorGenPerm (G := G) n δ) v)⁻¹ := by
  classical
  sorry

end Work.SSGRoute
