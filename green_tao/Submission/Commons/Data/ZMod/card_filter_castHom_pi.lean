import Mathlib
import Submission.Commons.Data.ZMod.card_castHom_fiber

namespace Commons.Data.ZMod

/-- Fibre-counting principle: if every fibre of `f : α → β` has cardinality `k`, then the
number of `a` with `S (f a)` is `k` times the number of `b` with `S b`. -/
theorem card_filter_comp_of_fiber_card {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (k : ℕ) (hf : ∀ b : β, (Finset.univ.filter (fun a : α => f a = b)).card = k)
    (S : β → Prop) [DecidablePred S] :
    (Finset.univ.filter (fun a : α => S (f a))).card = k * (Finset.univ.filter S).card := by
  have key : (Finset.univ.filter (fun a : α => S (f a))).card
      = ∑ b ∈ Finset.univ.filter S, (Finset.univ.filter (fun a : α => f a = b)).card := by
    have h1 : (Finset.univ.filter (fun a : α => S (f a))).card
        = (Finset.univ.filter (fun a : α => f a ∈ Finset.univ.filter S)).card := by
      congr 1; ext a; simp
    rw [h1, ← Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset α)
      (Finset.univ.filter S) f]
  rw [key, Finset.sum_const_nat (fun b (_ : b ∈ Finset.univ.filter S) => hf b), Nat.mul_comm]

/-- Every fibre of the coordinatewise reduction map `(Fin t → ZMod n) → (Fin t → ZMod m)`
has cardinality `(n / m) ^ t`. -/
theorem card_fiber_castHom_pi {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n) {t : ℕ}
    (y : Fin t → ZMod m) :
    (Finset.univ.filter (fun x : Fin t → ZMod n =>
      (fun j => ZMod.castHom h (ZMod m) (x j)) = y)).card = (n / m) ^ t := by
  classical
  rw [← Fintype.card_subtype]
  calc Fintype.card {x : Fin t → ZMod n // (fun j => ZMod.castHom h (ZMod m) (x j)) = y}
      = Fintype.card {x : Fin t → ZMod n // ∀ j, ZMod.castHom h (ZMod m) (x j) = y j} :=
        Fintype.card_congr (Equiv.subtypeEquivRight (fun x => funext_iff))
    _ = Fintype.card (∀ j : Fin t, {z : ZMod n // ZMod.castHom h (ZMod m) z = y j}) :=
        Fintype.card_congr (Equiv.subtypePiEquivPi (β := fun _ : Fin t => ZMod n)
          (p := fun (j : Fin t) (z : ZMod n) => ZMod.castHom h (ZMod m) z = y j))
    _ = ∏ j : Fin t, Fintype.card {z : ZMod n // ZMod.castHom h (ZMod m) z = y j} :=
        Fintype.card_pi
    _ = ∏ _j : Fin t, n / m := by
        apply Finset.prod_congr rfl
        intro j _
        rw [Fintype.card_subtype]
        exact card_castHom_fiber h (y j)
    _ = (n / m) ^ t := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_filter_castHom_pi {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n) {t : ℕ}
    (S : (Fin t → ZMod m) → Prop) [DecidablePred S] :
    (Finset.univ.filter (fun x : Fin t → ZMod n =>
      S (fun j => ZMod.castHom h (ZMod m) (x j)))).card
      = (n / m) ^ t * (Finset.univ.filter S).card := by
  classical
  exact card_filter_comp_of_fiber_card
    (fun x : Fin t → ZMod n => fun j => ZMod.castHom h (ZMod m) (x j))
    ((n / m) ^ t) (fun y => card_fiber_castHom_pi h y) S

end Commons.Data.ZMod
