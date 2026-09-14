import Mathlib
import Submission.Vdw.Counting

open Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Box counts of polynomials by their reductions modulo `m` (Case-I first stone)

Case I of the proof of Theorem 1 (Bhargava §5, `CaseI.lean`) needs to bound
the number of box polynomials whose reduction modulo a modulus `m` lies in a
given set `S` of residue classes: such polynomials number at most
`|S| · ((2H+1)/m + 1)^n`, because among the `2H+1` consecutive integers
`|z| ≤ H` a fixed residue class modulo `m` occurs at most `(2H+1)/m + 1`
times.

The elementary "modulus smaller than the box side" step of Case I (`C < H`)
combines this transfer lemma with a bound on `|S|` (the number of monic
degree-`n` residue classes of index `≥ k_p`, `O(∏_p c·p^{n−k_p})`) to get the
per-discriminant estimate `O(c^{ω(D)}H^n/D)`.
-/

namespace Submission.Vdw

noncomputable section

/-- The reduction map of a box polynomial: its `n` non-leading coefficients
modulo `m`. -/
def boxResidue (n H m : ℕ) (p : ↥(Box n H)) : Fin n → ZMod m :=
  fun i => ((p : ℤ[X]).coeff i.1 : ZMod m)

/-- The naturals `k < N` lying in the residue class of the canonical
representative `c0 < m` modulo `m` number at most `N/m + 1`: each is
`m·(k/m) + c0`, so `k ↦ k/m` is injective into `Fin (N/m+1)`. -/
private lemma card_congruent_range_modEq_le (N m : ℕ) (c0 : ℕ) (hc0 : c0 < m) :
    Nat.card {k : Fin N // (k : ℕ) ≡ c0 [MOD m]} ≤ N / m + 1 := by
  classical
  let f : {k : Fin N // (k : ℕ) ≡ c0 [MOD m]} → Fin (N / m + 1) := fun k =>
    ⟨(k : Fin N).val / m, by
      have hv : (k : Fin N).val < N := (k : Fin N).isLt
      have hq : (k : Fin N).val / m ≤ N / m := Nat.div_le_div_right (Nat.le_of_lt hv)
      omega⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Fin.ext
    have hmod₁ : (a : Fin N).val % m = c0 := by
      have h₁ : (a : Fin N).val % m = c0 % m := by
        simpa [Nat.ModEq] using (a.2 : (a : Fin N).val ≡ c0 [MOD m])
      exact h₁.trans (Nat.mod_eq_of_lt hc0)
    have hmod₂ : (b : Fin N).val % m = c0 := by
      have h₂ : (b : Fin N).val % m = c0 % m := by
        simpa [Nat.ModEq] using (b.2 : (b : Fin N).val ≡ c0 [MOD m])
      exact h₂.trans (Nat.mod_eq_of_lt hc0)
    have hq : (a : Fin N).val / m = (b : Fin N).val / m := by
      exact congrArg (fun x : Fin (N / m + 1) => (x : ℕ)) hab
    calc
      (a : Fin N).val = m * ((a : Fin N).val / m) + (a : Fin N).val % m :=
        (Nat.div_add_mod (a : Fin N).val m).symm
      _ = m * ((b : Fin N).val / m) + (b : Fin N).val % m := by rw [hq, hmod₁, hmod₂]
      _ = (b : Fin N).val := Nat.div_add_mod (b : Fin N).val m
  haveI : Fintype {k : Fin N // (k : ℕ) ≡ c0 [MOD m]} := inferInstance
  rw [Nat.card_eq_fintype_card]
  simpa using (Fintype.card_le_of_injective f hinj)

/-- The naturals `k < N` lying in the residue class of `a : ZMod m` number at
most `N/m + 1`. -/
private lemma card_congruent_range_zmod_le (N m : ℕ) (_hm : 1 ≤ m) (a : ZMod m) :
    Nat.card {k : Fin N // ((k : ℕ) : ZMod m) = a} ≤ N / m + 1 := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  calc
    Nat.card {k : Fin N // ((k : ℕ) : ZMod m) = a}
        = Nat.card {k : Fin N // (k : ℕ) ≡ a.val [MOD m]} := by
          apply Nat.card_congr
          refine {
            toFun := fun k => ⟨k.1, ?_⟩
            invFun := fun k => ⟨k.1, ?_⟩
            left_inv := by intro k; apply Subtype.ext; rfl
            right_inv := by intro k; apply Subtype.ext; rfl }
          · have hc : (a : ZMod m) = ((a.val : ℕ) : ZMod m) :=
              (ZMod.natCast_zmod_val a).symm
            exact (ZMod.natCast_eq_natCast_iff (k.1 : ℕ) a.val m).mp (k.2.trans hc)
          · exact ((ZMod.natCast_eq_natCast_iff (k.1 : ℕ) a.val m).mpr k.2).trans
              (ZMod.natCast_zmod_val a)
    _ ≤ N / m + 1 := card_congruent_range_modEq_le N m a.val (ZMod.val_lt a)

/-- The shift `z ↦ z + H` identifies the bounded integers with `Fin (2H+1)`.
Its value, cast to `ZMod m`, is `z + H`. -/
private lemma bddIntToFin_val_zmod (H m : ℕ) (z : BddInt H) :
    (((bddIntToFin H z : Fin (2 * H + 1)) : ℕ) : ZMod m) =
      (z.1 : ZMod m) + (H : ZMod m) := by
  dsimp [bddIntToFin]
  have hnonneg : 0 ≤ z.1 + (H : ℤ) := by
    have hz := z.2
    rw [abs_le] at hz
    omega
  rw [← Int.cast_natCast]
  rw [Int.toNat_of_nonneg hnonneg]
  rw [Int.cast_add]
  simp

/-- The inverse shift `k ↦ k − H` sends `Fin (2H+1)` back to the bounded
integers; its value, cast to `ZMod m`, is `k − H`. -/
private lemma bddFinToInt_val_zmod (H m : ℕ) (k : Fin (2 * H + 1)) :
    (((bddFinToInt H k : BddInt H) : ℤ) : ZMod m) =
      ((k : ℕ) : ZMod m) - (H : ZMod m) := by
  dsimp [bddFinToInt]
  rw [Int.cast_sub]
  rw [Int.cast_natCast]
  rw [Int.cast_natCast]

/-- Among the integers of absolute value at most `H`, a fixed residue class
modulo `m` contains at most `(2H+1)/m + 1` elements. -/
theorem bddInt_congruent_card_le (H m : ℕ) (hm : 1 ≤ m) (c : ZMod m) :
    Nat.card {z : BddInt H // ((z : ℤ) : ZMod m) = c} ≤ (2 * H + 1) / m + 1 := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  calc
    Nat.card {z : BddInt H // ((z : ℤ) : ZMod m) = c}
        = Nat.card {k : Fin (2 * H + 1) // ((k : ℕ) : ZMod m) = c + (H : ZMod m)} := by
          apply Nat.card_congr
          refine {
            toFun := fun z => ⟨bddIntEquivFin H z.1, ?_⟩
            invFun := fun k => ⟨(bddIntEquivFin H).symm k.1, ?_⟩
            left_inv := by
              intro z
              apply Subtype.ext
              exact (bddIntEquivFin H).left_inv z.1
            right_inv := by
              intro k
              apply Subtype.ext
              exact (bddIntEquivFin H).right_inv k.1 }
          · have hk := bddIntToFin_val_zmod H m z.1
            change (((bddIntToFin H z.1 : Fin (2 * H + 1)) : ℕ) : ZMod m) = c + (H : ZMod m)
            rw [hk, z.2]
          · have hz := bddFinToInt_val_zmod H m k.1
            change (((bddFinToInt H k.1 : BddInt H) : ℤ) : ZMod m) = c
            rw [hz]
            have hk2 : c + (H : ZMod m) = (((k.1 : Fin (2 * H + 1)) : ℕ) : ZMod m) := by
              simpa using k.2.symm
            exact (eq_sub_of_add_eq hk2).symm
    _ ≤ (2 * H + 1) / m + 1 := card_congruent_range_zmod_le (2 * H + 1) m hm (c + (H : ZMod m))

/-- **Box fiber bound.**  For a fixed residue vector `r : Fin n → ZMod m`, the
box contains at most `((2H+1)/m + 1)^n` polynomials whose non-leading
coefficients are congruent to `r` modulo `m`. -/
theorem box_fiber_residue_le (n H m : ℕ) (hm : 1 ≤ m) (r : Fin n → ZMod m) :
    Nat.card {p : ↥(Box n H) // boxResidue n H m p = r} ≤ ((2 * H + 1) / m + 1) ^ n := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  let F : Type := {p : ↥(Box n H) // boxResidue n H m p = r}
  -- each box polynomial in the fiber injects into the product of per-coordinate fibers
  let g : F → (i : Fin n) → {z : BddInt H // ((z : ℤ) : ZMod m) = r i} := fun p i =>
    ⟨coeffVec p.1 i, by
      have hi := congrFun p.2 i
      simpa [coeffVec, boxResidue] using hi⟩
  have hInj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply coeffVec_injective n H
    funext i
    apply Subtype.ext
    have hva := congrArg (fun w : {z : BddInt H // ((z : ℤ) : ZMod m) = r i} => (w : BddInt H).1)
      (congrFun hab i)
    simpa using hva
  have hVfinite : Finite ((i : Fin n) → {z : BddInt H // ((z : ℤ) : ZMod m) = r i}) :=
    inferInstance
  calc
    Nat.card F
        ≤ Nat.card ((i : Fin n) → {z : BddInt H // ((z : ℤ) : ZMod m) = r i}) :=
          Nat.card_le_card_of_injective g hInj
    _ = ∏ i : Fin n, Nat.card {z : BddInt H // ((z : ℤ) : ZMod m) = r i} := Nat.card_pi
    _ ≤ ∏ i : Fin n, ((2 * H + 1) / m + 1) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact Nat.zero_le _
      · intro i hi
        exact bddInt_congruent_card_le H m hm (r i)
    _ = ((2 * H + 1) / m + 1) ^ n := by simp

/-- **Main transfer lemma (Case-I first stone).**  For a set `S` of residue
vectors modulo `m`, the number of box polynomials whose non-leading
coefficient residue vector lies in `S` is at most
`|S| · ((2H+1)/m + 1)^n`. -/
theorem box_residue_set_le (n H m : ℕ) (hm : 1 ≤ m) (S : Set (Fin n → ZMod m)) :
    Nat.card {p : ↥(Box n H) // boxResidue n H m p ∈ S} ≤
      S.ncard * ((2 * H + 1) / m + 1) ^ n := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  let γ : Type := Fin n → ZMod m
  let α : Type := ↥(Box n H)
  let X : Type := {p : α // boxResidue n H m p ∈ S}
  let Y : Type := {s : γ // s ∈ S}
  let f : X → Y := fun p => ⟨boxResidue n H m p.1, p.2⟩
  haveI : Fintype Y := inferInstance
  haveI (y : Y) : Fintype {x : X // f x = y} := inferInstance
  -- S.ncard is the cardinality of Y
  have hS : S.ncard = Nat.card Y := by
    simpa [Y] using (ncard_eq_natCard S)
  -- every fiber of f : X → Y has cardinality at most ((2H+1)/m+1)^n
  have hfibN (y : Y) : Nat.card {x : X // f x = y} ≤ ((2 * H + 1) / m + 1) ^ n := by
    let e2 : {x : X // f x = y} ≃ {p : ↥(Box n H) // boxResidue n H m p = y.1} := by
      refine {
        toFun := fun x => ⟨x.1.1, ?_⟩
        invFun := fun p => ⟨⟨p.1, ?_⟩, ?_⟩
        left_inv := by
          intro x
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := by
          intro p
          apply Subtype.ext
          rfl }
      · have hx := congrArg (fun w : Y => w.1) x.2
        simpa [f] using hx
      · rw [p.2]
        exact y.2
      · apply Subtype.ext
        exact p.2
    have h := box_fiber_residue_le n H m hm y.1
    calc
      Nat.card {x : X // f x = y} =
          Nat.card {p : ↥(Box n H) // boxResidue n H m p = y.1} := Nat.card_congr e2
      _ ≤ ((2 * H + 1) / m + 1) ^ n := h
  -- X is the disjoint union over s ∈ S of these fibers
  have hX : Nat.card X = ∑ y : Y, Nat.card {x : X // f x = y} := by
    calc
      Nat.card X = Nat.card (Sigma (fun y : Y => {x : X // f x = y})) :=
        (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
      _ = ∑ y : Y, Nat.card {x : X // f x = y} := Nat.card_sigma
  calc
    Nat.card {p : ↥(Box n H) // boxResidue n H m p ∈ S} ≤ S.ncard * ((2 * H + 1) / m + 1) ^ n := by
      calc
        Nat.card {p : ↥(Box n H) // boxResidue n H m p ∈ S} = ∑ y : Y, Nat.card {x : X // f x = y} := by
          simpa [X, α] using hX
        _ ≤ ∑ y : Y, ((2 * H + 1) / m + 1) ^ n := by
          apply Finset.sum_le_sum
          intro y hy
          exact hfibN y
        _ = Nat.card Y * ((2 * H + 1) / m + 1) ^ n := by
          rw [Finset.sum_const, Finset.card_univ]
          simp [Nat.card_eq_fintype_card]
        _ = S.ncard * ((2 * H + 1) / m + 1) ^ n := by rw [← hS]

end
end Submission.Vdw
