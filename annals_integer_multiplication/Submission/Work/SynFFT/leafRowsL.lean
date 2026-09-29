import Mathlib
import Submission.Work.SynFFT.axisLeafDefs

/-!
# `Work.SynFFT.leafRowsL`

Pure list bookkeeping for the leaf step of the blockwise transpose (`axisLeafDefs`):

* `lfRowsL t B W P` is the row-list accumulator after having processed the prefix `P` of `W`
  (the list of completed row values, in accumulation order, i.e. reversed);
* `lfRowL B P` is the current (partial) row accumulator.

The three conjuncts are exactly the step lemmas of the loop of `lfLoop`: an element that does not
close a row leaves `lfRowsL` unchanged, an element that closes a row `cons`es the completed row
value onto the row list and resets the row accumulator, and at the end (`P = W`) the accumulator is
the reversed list of row values of `W`.
-/

namespace Work.SynFFT

open HvdH

/-! ## Auxiliary arithmetic and list lemmas -/

/-- Carries of the row counter `B - (row length)`: dividing the prefix length by `B` and stepping
by one element. -/
private theorem leafRowsLNat (B n : ℕ) (hB : 1 ≤ B) :
    ((n + 1) / B = n / B ↔ n % B + 1 < B) ∧
    (n % B = B - 1 → (n + 1) / B = n / B + 1) ∧
    (n % B = B - 1 → (n + 1) % B = 0) ∧
    (n % B + 1 < B → (n + 1) % B = n % B + 1) := by
  have hB0 : 0 < B := hB
  have hsucc : n + 1 = (n % B + 1) + B * (n / B) := by
    have h := Nat.mod_add_div n B
    omega
  have hdiv : (n + 1) / B = (n % B + 1) / B + n / B := by
    rw [hsucc, Nat.add_mul_div_left _ _ hB0]
  have hmod' : (n + 1) % B = (n % B + 1) % B := by
    rw [hsucc, Nat.add_mul_mod_self_left]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdiv]
    constructor
    · intro h
      have h0 : (n % B + 1) / B = 0 := by omega
      rw [Nat.div_eq_zero_iff_lt hB0] at h0
      exact h0
    · intro h
      have h0 : (n % B + 1) / B = 0 := by
        rw [Nat.div_eq_zero_iff_lt hB0]
        exact h
      omega
  · intro h
    have hr : n % B + 1 = B := by omega
    rw [hdiv, hr, Nat.div_self hB0]
    omega
  · intro h
    have hr : n % B + 1 = B := by omega
    rw [hmod', hr, Nat.mod_self]
  · intro h
    rw [hmod', Nat.mod_eq_of_lt h]

/-- One more element of the row decomposition: `take (k+1)` appends the `k`-th chunk. -/
private theorem rowsOf_take_succ (t B : ℕ) (W : List Val) (k : ℕ) (hk : k < t) :
    (rowsOf t B W).take (k + 1) = (rowsOf t B W).take k ++ [(W.drop (k * B)).take B] := by
  have hrk : (List.range t).take (k + 1) = (List.range t).take k ++ [k] := by
    have hlen : k < (List.range t).length := by rw [List.length_range]; exact hk
    have h := List.take_succ_eq_append_getElem (l := List.range t) (i := k) hlen
    simpa using h
  have h1 : (rowsOf t B W).take (k + 1)
      = ((List.range t).take (k + 1)).map (fun j => (W.drop (j * B)).take B) := by
    unfold rowsOf
    rw [← List.map_take]
  have h2 : (rowsOf t B W).take k
      = ((List.range t).take k).map (fun j => (W.drop (j * B)).take B) := by
    unfold rowsOf
    rw [← List.map_take]
  simp only [h1, h2, hrk, List.map_append, List.map_cons, List.map_nil]

/-- The `k`-th chunk of `W = P ++ [x] ++ l'` when `x` is the last element of the `k`-th row
(`k = P.length / B`): it is the partial row of `P` followed by `x`. -/
private theorem lfDropTake (B : ℕ) (P l' : List Val) (x : Val)
    (hB : 1 ≤ B) (hmod : P.length % B = B - 1) :
    (((P ++ [x] ++ l').drop (P.length / B * B)).take B) = P.drop (P.length / B * B) ++ [x] := by
  have hle : P.length / B * B ≤ P.length := Nat.div_mul_le_self _ _
  have hsub : P.length - P.length / B * B = B - 1 := by
    have h := Nat.div_add_mod' P.length B
    omega
  have hlen : (P.drop (P.length / B * B)).length = B - 1 := by
    rw [List.length_drop, hsub]
  have hdrop : (P ++ [x] ++ l').drop (P.length / B * B)
      = P.drop (P.length / B * B) ++ ([x] ++ l') := by
    simp only [List.append_assoc]
    exact List.drop_append_of_le_length hle
  have hlenB : (P.drop (P.length / B * B)).length ≤ B := by rw [hlen]; omega
  have htakeP : (P.drop (P.length / B * B)).take B = P.drop (P.length / B * B) :=
    List.take_of_length_le hlenB
  have h1 : B - (P.drop (P.length / B * B)).length = 1 := by rw [hlen]; omega
  have htakeX : ([x] ++ l').take (B - (P.drop (P.length / B * B)).length) = [x] := by
    rw [h1]; simp
  rw [hdrop, List.take_append, htakeP, htakeX]

/-- `lfRV` of a row closed by `x` is `ofList (lfWrap x :: lfRowL B P)`. -/
private theorem lfRV_append_singleton (B : ℕ) (P : List Val) (x : Val) :
    lfRV (P.drop (P.length / B * B) ++ [x]) = ofList (lfWrap x :: lfRowL B P) := by
  unfold lfRV lfRowL
  congr 1
  rw [List.reverse_append, List.map_append]
  simp

/-! ## The step lemmas of the leaf loop -/

theorem leafRowsL :
    (∀ (t B : ℕ) (W P : List HvdH.Val) (x : HvdH.Val), 1 ≤ B → P.length % B < B - 1 →
      Work.SynFFT.lfRowsL t B W (P ++ [x]) = Work.SynFFT.lfRowsL t B W P) ∧
    (∀ (t B : ℕ) (W P l' : List HvdH.Val) (x : HvdH.Val), 1 ≤ B → W = P ++ [x] ++ l' →
      P.length < t * B → P.length % B = B - 1 →
      Work.SynFFT.lfRowsL t B W (P ++ [x]) =
        HvdH.ofList (Work.SynFFT.lfWrap x :: Work.SynFFT.lfRowL B P) ::
          Work.SynFFT.lfRowsL t B W P) ∧
    (∀ (t B : ℕ) (W : List HvdH.Val), 1 ≤ B → W.length = t * B →
      Work.SynFFT.lfRowsL t B W W = (List.map Work.SynFFT.lfRV (rowsOf t B W)).reverse) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t B W P x hB hmod
    have hlt : P.length % B + 1 < B := by omega
    have hk : (P.length + 1) / B = P.length / B := (leafRowsLNat B P.length hB).1.mpr hlt
    have hlen : (P ++ [x]).length = P.length + 1 := by simp
    unfold lfRowsL
    rw [hlen, hk]
  · intro t B W P l' x hB hW hlt hmod
    have hB0 : 0 < B := hB
    have hk : (P.length + 1) / B = P.length / B + 1 := (leafRowsLNat B P.length hB).2.1 hmod
    have hlen : (P ++ [x]).length = P.length + 1 := by simp
    subst hW
    have hkt : P.length / B < t := by
      have hdecomp : P.length / B * B + P.length % B = P.length := Nat.div_add_mod' P.length B
      have hlt' : P.length / B * B < t * B := by omega
      exact (Nat.mul_lt_mul_right hB0).mp hlt'
    unfold lfRowsL
    rw [hlen, hk]
    rw [rowsOf_take_succ t B (P ++ [x] ++ l') (P.length / B) hkt]
    rw [List.map_append, List.map_cons, List.map_nil]
    rw [lfDropTake B P l' x hB hmod]
    rw [lfRV_append_singleton B P x]
    simp [List.reverse_append]
  · intro t B W hB hlen
    have hB0 : 0 < B := hB
    have hk : W.length / B = t := by rw [hlen, Nat.mul_div_left t hB0]
    have htake : (rowsOf t B W).take t = rowsOf t B W :=
      List.take_of_length_le (by simp [rowsOf])
    unfold lfRowsL
    rw [hk, htake]

end Work.SynFFT
