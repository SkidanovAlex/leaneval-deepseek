import Submission.ZagierHoffmanProof.StepD

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step D2: Prop 2.1 base cases in the combination form

Part 1 at depth (1,1): `S_d(x)·S_d(y) = S_d(x+y) + Σ_i Δ^i S_d(x+y-i, i)`
(paper (2.1) = diag_level, assembled into the P1W carrier).
Part 2 at depth (1,1): the depth-one `S_<d` stuffle (S_lt_one_stuffle → S_lt_one_mul_eq,
assembled into the P2W carrier).

Index sets are `PUnit ⊕ Fin (x+y-1)` (resp. with three `PUnit`s), so all `Fintype`
instances are the standard ones.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Helper: the finite index type of Part-1's (1,1) expansion. -/
abbrev P1Idx (x y : ℕ+) := PUnit.{1} ⊕ Fin ((x : ℕ) + (y : ℕ) - 1)

/-- Helper: the finite index type of Part-2's (1,1) expansion. -/
abbrev P2Idx (x y : ℕ+) := PUnit.{1} ⊕ PUnit.{1} ⊕ PUnit.{1} ⊕ Fin ((x : ℕ) + (y : ℕ) - 1)

/-- Part 1 base case: depth-1 × depth-1 (paper (2.5) from (2.1)). -/
theorem part1_base (x y : ℕ+) :
    P1W F 1 1 (by omega : 0 < 1) (by omega : 0 < 1) (single x) (single y) := by
  classical
  let dep : P1Idx x y → ℕ := fun t => match t with | Sum.inl _ => 1 | Sum.inr _ => 2
  have hdep : ∀ t : P1Idx x y, 0 < dep t := by
    intro t
    cases t <;> simp [dep]
  let f : P1Idx x y → ℤ := fun t => match t with
    | Sum.inl _ => (1 : ℤ)
    | Sum.inr j => ChenDeltaZ F (x : ℕ) (y : ℕ) (j.1 + 1)
  let c : ∀ t : P1Idx x y, Fin (dep t) → ℕ+ := fun t => match t with
    | Sum.inl _ => single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩
    | Sum.inr j => thakurExp (x : ℕ) (y : ℕ) ⟨j.1 + 1, by
        have hj : j.1 < (x : ℕ) + (y : ℕ) - 1 := j.2
        simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (x : ℕ) + (y : ℕ) - 1)⟩
  refine ⟨P1Idx x y, ?_, dep, hdep, f, c, ?hid, ?hle, ?hbd⟩
  · infer_instance
  · intro d
    calc
      S F 1 (by omega) (single x) d * S F 1 (by omega) (single y) d
          = S F 1 (by omega)
              (single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) d +
            ∑ j : Fin ((x : ℕ) + (y : ℕ) - 1),
              ((ChenDeltaZ F (x : ℕ) (y : ℕ) (j.1 + 1) : ℤ) : RatFunc.CompletionAtInfty F) *
              S F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) ⟨j.1 + 1, by
                have hj : j.1 < (x : ℕ) + (y : ℕ) - 1 := j.2
                simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (x : ℕ) + (y : ℕ) - 1)⟩) d :=
            S_one_mul_eq_fin F x y d
      _ = (∑ a : P1Idx x y, ((f a : ℤ) : RatFunc.CompletionAtInfty F) *
            S F (dep a) (hdep a) (c a) d) := by
            symm
            have hs : (∑ a : P1Idx x y, ((f a : ℤ) : RatFunc.CompletionAtInfty F) *
                S F (dep a) (hdep a) (c a) d) =
                S F 1 (by omega)
                  (single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) d +
                ∑ j : Fin ((x : ℕ) + (y : ℕ) - 1),
                  ((ChenDeltaZ F (x : ℕ) (y : ℕ) (j.1 + 1) : ℤ) : RatFunc.CompletionAtInfty F) *
                  S F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) ⟨j.1 + 1, by
                    have hj : j.1 < (x : ℕ) + (y : ℕ) - 1 := j.2
                    simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (x : ℕ) + (y : ℕ) - 1)⟩) d := by
                calc
                  (∑ a : P1Idx x y, ((f a : ℤ) : RatFunc.CompletionAtInfty F) *
                      S F (dep a) (hdep a) (c a) d)
                      = (∑ u : PUnit, ((f (Sum.inl u) : ℤ) : RatFunc.CompletionAtInfty F) *
                            S F (dep (Sum.inl u)) (hdep (Sum.inl u)) (c (Sum.inl u)) d) +
                        (∑ j : Fin ((x : ℕ) + (y : ℕ) - 1),
                          ((f (Sum.inr j) : ℤ) : RatFunc.CompletionAtInfty F) *
                          S F (dep (Sum.inr j)) (hdep (Sum.inr j)) (c (Sum.inr j)) d) := by
                        exact Fintype.sum_sum_type (f := fun a : P1Idx x y =>
                          ((f a : ℤ) : RatFunc.CompletionAtInfty F) * S F (dep a) (hdep a) (c a) d)
                  _ = ((f (Sum.inl PUnit.unit) : ℤ) : RatFunc.CompletionAtInfty F) *
                        S F (dep (Sum.inl PUnit.unit)) (hdep (Sum.inl PUnit.unit)) (c (Sum.inl PUnit.unit)) d +
                      (∑ j : Fin ((x : ℕ) + (y : ℕ) - 1),
                        ((f (Sum.inr j) : ℤ) : RatFunc.CompletionAtInfty F) *
                        S F (dep (Sum.inr j)) (hdep (Sum.inr j)) (c (Sum.inr j)) d) := by
                        simp
                  _ = S F 1 (by omega)
                        (single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) d +
                      ∑ j : Fin ((x : ℕ) + (y : ℕ) - 1),
                        ((ChenDeltaZ F (x : ℕ) (y : ℕ) (j.1 + 1) : ℤ) : RatFunc.CompletionAtInfty F) *
                        S F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) ⟨j.1 + 1, by
                          have hj : j.1 < (x : ℕ) + (y : ℕ) - 1 := j.2
                          simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (x : ℕ) + (y : ℕ) - 1)⟩) d := by
                        simp [f, dep, c]
            exact hs
  · intro a
    cases a with
    | inl u => simpa [c, dep] using LePad_single_of_sum x y
    | inr j => simpa [c, dep] using LePad_thakurExp_of_sum x y ⟨j.1 + 1, by
                  have hj : j.1 < (x : ℕ) + (y : ℕ) - 1 := j.2
                  simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (x : ℕ) + (y : ℕ) - 1)⟩
  · intro a
    cases a with
    | inl u => simp [dep]
    | inr j => simp [dep]

/-- Part 2 base case: depth-1 × depth-1 (paper (2.6) from (2.4)). -/
theorem part2_base (x y : ℕ+) :
    P2W F 1 1 (by omega : 0 < 1) (by omega : 0 < 1) (single x) (single y) := by
  classical
  let dep : P2Idx x y → ℕ := fun t => match t with
    | Sum.inl _ => 2
    | Sum.inr (Sum.inl _) => 2
    | Sum.inr (Sum.inr (Sum.inl _)) => 1
    | Sum.inr (Sum.inr (Sum.inr _)) => 2
  have hdep : ∀ t : P2Idx x y, 0 < dep t := by
    intro t
    cases t with
    | inl u => simp [dep]
    | inr t2 => cases t2 with
      | inl u => simp [dep]
      | inr t3 => cases t3 with
        | inl u => simp [dep]
        | inr j => simp [dep]
  let f : P2Idx x y → ℤ := fun t => match t with
    | Sum.inl _ => (1 : ℤ)
    | Sum.inr (Sum.inl _) => (1 : ℤ)
    | Sum.inr (Sum.inr (Sum.inl _)) => (1 : ℤ)
    | Sum.inr (Sum.inr (Sum.inr j)) => ChenDeltaZ F (x : ℕ) (y : ℕ) (j.1 + 1)
  let c : ∀ t : P2Idx x y, Fin (dep t) → ℕ+ := fun t => match t with
    | Sum.inl _ => pair x y
    | Sum.inr (Sum.inl _) => pair y x
    | Sum.inr (Sum.inr (Sum.inl _)) =>
        single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩
    | Sum.inr (Sum.inr (Sum.inr j)) => thakurExp (x : ℕ) (y : ℕ) ⟨j.1 + 1, by
        have hj : j.1 < (x : ℕ) + (y : ℕ) - 1 := j.2
        simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (x : ℕ) + (y : ℕ) - 1)⟩
  refine ⟨P2Idx x y, ?_, dep, hdep, f, c, ?hid, ?hle, ?hbd⟩
  · infer_instance
  · intro d
    let G : P2Idx x y → RatFunc.CompletionAtInfty F := fun a =>
      ((f a : ℤ) : RatFunc.CompletionAtInfty F) * S_lt F (dep a) (hdep a) (c a) d
    have h1 : (∑ a : P2Idx x y, G a) =
        G (Sum.inl PUnit.unit) + ∑ b : PUnit ⊕ PUnit ⊕ Fin ((x : ℕ) + (y : ℕ) - 1), G (Sum.inr b) := by
      have hsum := Fintype.sum_sum_type (f := G)
      rw [hsum]
      simp
    have h2 : (∑ b : PUnit ⊕ PUnit ⊕ Fin ((x : ℕ) + (y : ℕ) - 1), G (Sum.inr b)) =
        G (Sum.inr (Sum.inl PUnit.unit)) +
          ∑ w : PUnit ⊕ Fin ((x : ℕ) + (y : ℕ) - 1), G (Sum.inr (Sum.inr w)) := by
      have hsum := Fintype.sum_sum_type
        (f := fun b : PUnit ⊕ (PUnit ⊕ Fin ((x : ℕ) + (y : ℕ) - 1)) => G (Sum.inr b))
      rw [hsum]
      simp
    have h3 : (∑ w : PUnit ⊕ Fin ((x : ℕ) + (y : ℕ) - 1), G (Sum.inr (Sum.inr w))) =
        G (Sum.inr (Sum.inr (Sum.inl PUnit.unit))) +
          ∑ j : Fin ((x : ℕ) + (y : ℕ) - 1), G (Sum.inr (Sum.inr (Sum.inr j))) := by
      have hsum := Fintype.sum_sum_type
        (f := fun w : PUnit ⊕ Fin ((x : ℕ) + (y : ℕ) - 1) => G (Sum.inr (Sum.inr w)))
      rw [hsum]
      simp
    have hs : (∑ a : P2Idx x y, G a) =
        S_lt F 2 (by omega) (pair x y) d +
          S_lt F 2 (by omega) (pair y x) d +
          S_lt F 1 (by omega)
            (single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) d +
          ∑ j : Fin ((x : ℕ) + (y : ℕ) - 1),
            ((ChenDeltaZ F (x : ℕ) (y : ℕ) (j.1 + 1) : ℤ) : RatFunc.CompletionAtInfty F) *
            S_lt F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) ⟨j.1 + 1, by
              have hj : j.1 < (x : ℕ) + (y : ℕ) - 1 := j.2
              simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (x : ℕ) + (y : ℕ) - 1)⟩) d := by
      rw [h1, h2, h3]
      simp [f, dep, c, G]
      ac_rfl
    calc
      S_lt F 1 (by omega) (single x) d * S_lt F 1 (by omega) (single y) d
          = S_lt F 2 (by omega) (pair x y) d +
              S_lt F 2 (by omega) (pair y x) d +
              S_lt F 1 (by omega)
                (single ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) d +
              ∑ j : Fin ((x : ℕ) + (y : ℕ) - 1),
                ((ChenDeltaZ F (x : ℕ) (y : ℕ) (j.1 + 1) : ℤ) : RatFunc.CompletionAtInfty F) *
                S_lt F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) ⟨j.1 + 1, by
                  have hj : j.1 < (x : ℕ) + (y : ℕ) - 1 := j.2
                  simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (x : ℕ) + (y : ℕ) - 1)⟩) d :=
            S_lt_one_mul_eq_fin F x y d
      _ = (∑ a : P2Idx x y, G a) := by
            exact hs.symm
  · intro a
    cases a with
    | inl u => simpa [c, dep] using LePad_pair_of_sum x y
    | inr a2 => cases a2 with
      | inl u => simpa [c, dep] using LePad_pair_swap_of_sum x y
      | inr a3 => cases a3 with
        | inl u => simpa [c, dep] using LePad_single_of_sum x y
        | inr j => simpa [c, dep] using LePad_thakurExp_of_sum x y ⟨j.1 + 1, by
            have hj : j.1 < (x : ℕ) + (y : ℕ) - 1 := j.2
            simpa [Finset.mem_Icc] using (by omega : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ (x : ℕ) + (y : ℕ) - 1)⟩
  · intro a
    cases a with
    | inl u => simp [dep]
    | inr a2 => cases a2 with
      | inl u => simp [dep]
      | inr a3 => cases a3 with
        | inl u => simp [dep]
        | inr j => simp [dep]
end ZagierHoffmanPositiveChar
