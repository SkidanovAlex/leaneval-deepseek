import Mathlib
import Submission.Work.Resample.axKit
import Submission.Work.Resample.tensorAux

/-!
# The block splitting of one axis pass

`Work.Resample.axisList A m n B Φ es` applies the slice map `Φ` to every one of the `A * B` slices
(of length `m`) of the flat array `es` and reassembles the results (of length `n`) into a flat array
of shape `A × n × B`.

Splitting the outer product `A = X * t` splits the array into `t` consecutive blocks of shape
`X × m × B`; since every slice of the big array lies inside a single block (the outer index `a` of
the big array decomposes as `a = g * X + a'`), the pass commutes with the splitting.  This is
`axisList_blkAlt`.

The two ingredients are the entrywise description `axisList_getD` of one pass, and the index
arithmetic of `Nat` division and remainder.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Resample

open HvdH

/-! ## Reading the layout combinators -/

/-- The `s`-th slice of the flat `A × m × B` array `es`, as a `getD`-read. -/
lemma slices_getD_slice (A m B : ℕ) (es : List (ℤ × ℤ)) (s : ℕ) (hs : s < A * B) :
    (HvdH.slices A m B es).getD s []
      = (List.range m).map (fun j => es.getD ((s / B * m + j) * B + s % B) default) := by
  unfold HvdH.slices
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hs, Option.map_some,
    Option.getD_some]

/-- Entry `i` of slice `s` of the flat `A × m × B` array `es` (`getD`-read, so no length
hypothesis is needed). -/
lemma slices_getD_row (A m B : ℕ) (es : List (ℤ × ℤ)) (s i : ℕ) (hs : s < A * B) (hi : i < m) :
    ((HvdH.slices A m B es).getD s []).getD i (0,0)
      = es.getD ((s / B * m + i) * B + s % B) (0,0) := by
  rw [slices_getD_slice A m B es s hs]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some]
  rfl

/-- Entry `idx` of the flat `A × n × B` array `outs`. -/
lemma unslices_getD (A n B : ℕ) (outs : List (List (ℤ × ℤ))) (idx : ℕ) (hidx : idx < A * n * B) :
    (HvdH.unslices A n B outs).getD idx (0,0)
      = (outs.getD (idx / (n * B) * B + idx % B) []).getD (idx / B % n) (0,0) := by
  unfold HvdH.unslices
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hidx, Option.map_some,
    Option.getD_some]
  rfl

/-- The entrywise description of one axis pass: at index `idx < A * n * B`, the value is `Φ`
applied to the slice `j ↦ es[(idx/(n*B)*m + j)*B + idx%B]`, at row `idx/B % n`. -/
lemma axisList_getD (A m n B : ℕ) (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ)) (es : List (ℤ × ℤ))
    (hn : 0 < n) (hB : 0 < B) (idx : ℕ) (hidx : idx < A * n * B) :
    (axisList A m n B Φ es).getD idx (0,0) =
      Φ (fun j : Fin m => es.getD ((idx / (n * B) * m + (j : ℕ)) * B + idx % B) (0,0))
        ⟨idx / B % n, Nat.mod_lt _ hn⟩ := by
  have hnB : 0 < n * B := Nat.mul_pos hn hB
  have hs : idx / (n * B) * B + idx % B < A * B := by
    have h1 : idx / (n * B) < A :=
      (Nat.div_lt_iff_lt_mul hnB).mpr (by rwa [Nat.mul_assoc] at hidx)
    have h3 : idx / (n * B) * B + idx % B < (idx / (n * B) + 1) * B := by
      rw [Nat.add_mul]
      have := Nat.mod_lt idx hB
      omega
    have h4 : (idx / (n * B) + 1) * B ≤ A * B :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h1)
    omega
  have hdiv : (idx / (n * B) * B + idx % B) / B = idx / (n * B) := by
    rw [Nat.mul_comm (idx / (n * B)) B, Nat.mul_add_div hB,
      Nat.div_eq_of_lt (Nat.mod_lt _ hB), Nat.add_zero]
  have hmod : (idx / (n * B) * B + idx % B) % B = idx % B := by
    rw [Nat.mul_comm (idx / (n * B)) B, Nat.mul_add_mod,
      Nat.mod_eq_of_lt (Nat.mod_lt _ hB)]
  rw [axisList]
  rw [unslices_getD A n B _ idx hidx]
  have hslice : ((List.range (A * B)).map (fun s => List.ofFn (fun j : Fin n => Φ (fun i : Fin m =>
      ((HvdH.slices A m B es).getD s []).getD (i : ℕ) (0,0)) j))).getD
        (idx / (n * B) * B + idx % B) []
      = List.ofFn (fun j : Fin n => Φ (fun i : Fin m =>
          ((HvdH.slices A m B es).getD (idx / (n * B) * B + idx % B) []).getD (i : ℕ) (0,0)) j) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hs, Option.map_some,
      Option.getD_some]
  rw [hslice]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left (Nat.mod_lt _ hn),
    Option.getD_some]
  apply congrArg (fun g : Fin m → ℤ × ℤ => Φ g ⟨idx / B % n, Nat.mod_lt _ hn⟩)
  funext j
  rw [slices_getD_row A m B es (idx / (n * B) * B + idx % B) (j : ℕ) hs j.isLt, hdiv, hmod]

/-! ## Splitting the outer product -/

lemma idx_blk_bound {X m B a j K : ℕ} (ha : a < X) (hj : j < m) (hK : K < B) :
    (a * m + j) * B + K < (X * m) * B := by
  have h1 : (a * m + j) * B + K < (a * m + j) * B + B := Nat.add_lt_add_left hK _
  have h2 : (a * m + j) * B + B = (a * m + j + 1) * B := by ring
  have h4 : a * m + j + 1 ≤ (a + 1) * m := by rw [Nat.add_mul]; omega
  have h5 : (a + 1) * m ≤ X * m := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt ha)
  have h6 : (a * m + j + 1) * B ≤ (X * m) * B :=
    Nat.mul_le_mul_right _ (le_trans h4 h5)
  omega

theorem axisList_blkAlt (X t m n B : ℕ) (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ))
    (es : List (ℤ × ℤ)) (hn : 0 < n) (hB : 0 < B) :
    axisList (X * t) m n B Φ es =
      (List.range t).flatMap (fun g => axisList X m n B Φ (blk (X * m * B) g es)) := by
  have hlen : ∀ g < t, (axisList X m n B Φ (blk (X * m * B) g es)).length = X * n * B := by
    intro g _
    rw [axisList_length]
  have hlenR : ((List.range t).flatMap
      (fun g => axisList X m n B Φ (blk (X * m * B) g es))).length = (X * t) * n * B := by
    rw [flatMap_range_eq_map t (X * n * B)
      (fun g => axisList X m n B Φ (blk (X * m * B) g es)) hlen, List.length_map,
      List.length_range]
    ring
  rcases Nat.eq_zero_or_pos (X * n * B) with hX | hX
  · have hL : (axisList (X * t) m n B Φ es).length = 0 := by
      rw [axisList_length, show X * t * n * B = t * (X * n * B) from by ring, hX, Nat.mul_zero]
    have hR : ((List.range t).flatMap
        (fun g => axisList X m n B Φ (blk (X * m * B) g es))).length = 0 := by
      rw [hlenR, show X * t * n * B = t * (X * n * B) from by ring, hX, Nat.mul_zero]
    rw [List.eq_nil_of_length_eq_zero hL, List.eq_nil_of_length_eq_zero hR]
  · have hnB : 0 < n * B := Nat.mul_pos hn hB
    apply List.ext_getElem
    · rw [axisList_length, hlenR]
    · intro idx h1 h2
      have hidx : idx < (X * t) * n * B := by rwa [axisList_length] at h1
      have hidx2 : idx < (X * t) * n * B := by rw [← hlenR]; exact h2
      rw [List.getElem_eq_getD (h := h1) (0,0), List.getElem_eq_getD (h := h2) (0,0)]
      have hg : idx / (X * n * B) < t :=
        (Nat.div_lt_iff_lt_mul hX).mpr
          (by rw [show t * (X * n * B) = (X * t) * n * B from by ring]; exact hidx)
      have hx : idx % (X * n * B) < X * n * B := Nat.mod_lt _ hX
      set g := idx / (X * n * B) with hgdef
      set q := idx % (X * n * B) with hqdef
      have hdec : idx = g * (X * n * B) + q := by
        rw [hgdef, hqdef, Nat.mul_comm]
        exact (Nat.div_add_mod idx (X * n * B)).symm
      have hf1 : idx / (n * B) = g * X + q / (n * B) := by
        conv_lhs => rw [hdec]
        rw [show g * (X * n * B) = (n * B) * (g * X) from by ring]
        rw [Nat.mul_add_div hnB]
      have hf2 : idx % B = q % B := by
        conv_lhs => rw [hdec]
        rw [show g * (X * n * B) = B * (g * X * n) from by ring]
        rw [Nat.mul_add_mod]
      have hf3 : idx / B % n = q / B % n := by
        have hd : idx / B = g * (X * n) + q / B := by
          conv_lhs => rw [hdec]
          rw [show g * (X * n * B) = B * (g * (X * n)) from by ring]
          rw [Nat.mul_add_div hB]
        rw [hd, show g * (X * n) = n * (g * X) from by ring, Nat.mul_add_mod]
      rw [axisList_getD (X * t) m n B Φ es hn hB idx hidx, hf1, hf2]
      have hidxfin : (⟨idx / B % n, Nat.mod_lt (idx / B) hn⟩ : Fin n)
          = ⟨q / B % n, Nat.mod_lt (q / B) hn⟩ := Fin.ext hf3
      rw [hidxfin]
      conv_rhs => rw [hdec]
      rw [flatMap_getD t (X * n * B) (fun g => axisList X m n B Φ (blk (X * m * B) g es))
        hlen g q hg hx]
      rw [axisList_getD X m n B Φ (blk (X * m * B) g es) hn hB q hx]
      apply congrArg (fun h : Fin m → ℤ × ℤ => Φ h ⟨q / B % n, Nat.mod_lt (q / B) hn⟩)
      funext j
      rw [blk_getD (X * m * B) g ((q / (n * B) * m + (j : ℕ)) * B + q % B) es
        (idx_blk_bound
          ((Nat.div_lt_iff_lt_mul hnB).mpr (by rwa [Nat.mul_assoc] at hx))
          j.isLt (Nat.mod_lt q hB))]
      ring

end Work.Resample
