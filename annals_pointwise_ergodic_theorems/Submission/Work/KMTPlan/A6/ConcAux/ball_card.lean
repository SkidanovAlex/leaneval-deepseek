import Mathlib

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6.ConcAux

open Finset

/-- For naturals `u`, `v`: the classes of `u` and `v` modulo `p ^ m` agree if and only if `p ^ m`
divides the difference `u - v`. -/
lemma zmod_natCast_eq_iff_dvd (p m u v : ℕ) :
    ((u : ZMod (p ^ m)) = (v : ZMod (p ^ m))) ↔ (p : ℤ) ^ m ∣ (u : ℤ) - (v : ℤ) := by
  have h := ZMod.intCast_eq_intCast_iff_dvd_sub (v : ℤ) (u : ℤ) (p ^ m)
  rw [Int.natCast_pow] at h
  rw [eq_comm, ← Int.cast_natCast (R := ZMod (p ^ m)) v,
    ← Int.cast_natCast (R := ZMod (p ^ m)) u]
  exact h

/-- The `p`-adic ball of radius `p ^ m` inside `ℤ / p ^ k` has `p ^ (k - m)` elements. -/
theorem ball_card (p k m : ℕ) [Fact p.Prime] (hm : m ≤ k) (a : ZMod (p ^ k)) :
    (Finset.univ.filter (fun x : ZMod (p ^ k) =>
        (p : ℤ) ^ m ∣ ((x.val : ℤ) - (a.val : ℤ)))).card = p ^ (k - m) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  haveI : NeZero (p ^ m) := ⟨pow_ne_zero m hp.ne_zero⟩
  have hdvd : p ^ m ∣ p ^ k := pow_dvd_pow p hm
  let f : ZMod (p ^ k) →+* ZMod (p ^ m) := ZMod.castHom hdvd (ZMod (p ^ m))
  let g : ZMod (p ^ k) →+ ZMod (p ^ m) := f.toAddMonoidHom
  have hgval : ∀ x : ZMod (p ^ k), g x = (x.val : ZMod (p ^ m)) := by
    intro x
    show ZMod.castHom hdvd (ZMod (p ^ m)) x = (x.val : ZMod (p ^ m))
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  have hsurj : Function.Surjective g := ZMod.castHom_surjective hdvd
  -- The filtered set is the fibre of the reduction map `ZMod (p ^ k) → ZMod (p ^ m)`.
  have hset : (Finset.univ.filter (fun x : ZMod (p ^ k) =>
        (p : ℤ) ^ m ∣ ((x.val : ℤ) - (a.val : ℤ))))
      = Finset.univ.filter (fun x : ZMod (p ^ k) => g x = g a) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hgval x, hgval a]
    exact (zmod_natCast_eq_iff_dvd p m x.val a.val).symm
  have hfib : (Finset.univ.filter (fun x : ZMod (p ^ k) => g x = g a)).card
      = Fintype.card {x : ZMod (p ^ k) // g x = g a} :=
    (Fintype.card_subtype (fun x : ZMod (p ^ k) => g x = g a)).symm
  -- The fibre over `g a` is a translate of `ker g`.
  have e : {x : ZMod (p ^ k) // g x = g a} ≃ g.ker :=
    { toFun := fun x => ⟨x.1 - a, by
        rw [AddMonoidHom.mem_ker]
        simp [x.2]⟩
      invFun := fun y => ⟨y.1 + a, by
        simp [AddMonoidHom.mem_ker.mp y.2]⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  -- `ker g` has index `p ^ m` (Lagrange, the quotient being `ZMod (p ^ m)`).
  have hindex : g.ker.index = p ^ m := by
    have h1 : g.ker.index = Nat.card (⊤ : AddSubgroup (ZMod (p ^ m))) := by
      rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj]
    rw [h1, AddSubgroup.card_top, Nat.card_eq_fintype_card, ZMod.card]
  have hmul : Nat.card g.ker = p ^ (k - m) := by
    have h1 := AddSubgroup.index_mul_card g.ker
    rw [hindex] at h1
    rw [Nat.card_eq_fintype_card (α := ZMod (p ^ k)), ZMod.card] at h1
    have h2 : p ^ m * p ^ (k - m) = p ^ k := by
      rw [mul_comm, Nat.pow_sub_mul_pow p hm]
    have h3 : p ^ m * Nat.card g.ker = p ^ m * p ^ (k - m) := by rw [h1, h2]
    exact Nat.mul_left_cancel (Nat.pow_pos hp.pos) h3
  calc (Finset.univ.filter (fun x : ZMod (p ^ k) =>
        (p : ℤ) ^ m ∣ ((x.val : ℤ) - (a.val : ℤ)))).card
      = (Finset.univ.filter (fun x : ZMod (p ^ k) => g x = g a)).card := by rw [hset]
    _ = Fintype.card {x : ZMod (p ^ k) // g x = g a} := hfib
    _ = Nat.card {x : ZMod (p ^ k) // g x = g a} := (Nat.card_eq_fintype_card).symm
    _ = Nat.card g.ker := Nat.card_congr e
    _ = p ^ (k - m) := hmul

end Work.KMTPlan.A6.ConcAux
