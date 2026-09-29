import Mathlib
import Submission.Work.SB.BW2.Defs
import Submission.Work.SB.slicesFacts
import Submission.Work.SB.BW2.memFlattenSlices
import Submission.Work.SB.BW2.chunkArith

/-!
# Size bounds for the flattened `A × m × B` slices and their `m`-chunks

`Work.SB.BW2.vszFlatChunks` collects the three size facts needed by the `branchWord2` (slices
step) cost proof: every entry of `(slices A m B es).flatten` is an entry of `es` (hence has
`vsz ≤ L`), the whole flattened list encodes to at most `BIG N L`, and so does the list of its
consecutive `m`-chunks (up to the constant `4` of the cost bound).

The two combinatorial/arithmetic inputs are delegated:
* `Work.SB.BW2.memFlattenSlices`: an element of the flattening is an element of `es`;
* `Work.SB.BW2.chunkArith`: the two arithmetic estimates against `BIG`.
-/

namespace Work.SB.BW2

open HvdH

/-! ## Elementary `ofList` size bounds -/

/-- Unfolding of `vsz` at a `cons`. -/
private theorem vszCons (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc, Nat.add_assoc]

/-- `vsz` of a list value: one symbol per `cons`/`nil` plus the entries. -/
private theorem vsz_ofList_eq :
    ∀ xs : List Val, vsz (ofList xs) = (xs.map vsz).sum + xs.length + 1
  | [] => by simp [ofList, vsz, Val.enc]
  | x :: t => by
      have ih := vsz_ofList_eq t
      show vsz (Val.cons x (ofList t)) = _
      rw [vszCons, ih]
      simp [List.map_cons, List.sum_cons, List.length_cons]
      ring

/-- The sum of the sizes of the entries of a list is at most `length * B`. -/
private theorem sum_map_le (xs : List Val) (B : ℕ) (h : ∀ x ∈ xs, vsz x ≤ B) :
    (xs.map vsz).sum ≤ xs.length * B := by
  have h' : ∀ y ∈ xs.map vsz, y ≤ B := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact h x hx
  simpa [nsmul_eq_mul] using List.sum_le_card_nsmul (xs.map vsz) B h'

/-- `vsz` of a list value with entries of size `≤ B`. -/
private theorem vsz_ofList_le {xs : List Val} {B : ℕ} (h : ∀ x ∈ xs, vsz x ≤ B) :
    vsz (ofList xs) ≤ (xs.length + 1) * (B + 1) := by
  rw [vsz_ofList_eq]
  have h1 := sum_map_le xs B h
  have h2 : xs.length * B + xs.length + 1 ≤ (xs.length + 1) * (B + 1) := by nlinarith
  omega

/-- Sharper form: `vsz (ofList xs) = (xs.map vsz).sum + xs.length + 1 ≤ xs.length * B + xs.length + 1`. -/
private theorem vsz_ofList_le_mul {xs : List Val} {L : ℕ} (h : ∀ x ∈ xs, vsz x ≤ L) :
    vsz (ofList xs) ≤ xs.length * L + xs.length + 1 := by
  rw [vsz_ofList_eq]
  have h1 := sum_map_le xs L h
  omega

theorem vszFlatChunks (A m B N L : ℕ) (es : List HvdH.Val) (hm : 0 < m) (hAmB : A * m * B ≤ N)
    (hlen : es.length = A * m * B) (hv : ∀ x ∈ es, HvdH.vsz x ≤ L) :
    (∀ x ∈ (HvdH.slices A m B es).flatten, HvdH.vsz x ≤ L) ∧
    HvdH.vsz (HvdH.ofList ((HvdH.slices A m B es).flatten)) ≤ Work.SB.BW2.BIG N L ∧
    HvdH.vsz (HvdH.ofList ((List.range ((HvdH.slices A m B es).flatten.length / m)).map
        (fun i => HvdH.ofList (((HvdH.slices A m B es).flatten.drop (i * m)).take m)))) ≤
      4 * Work.SB.BW2.BIG N L := by
  obtain ⟨-, -, hSflat, -, -, -⟩ := Work.SB.slicesFacts A m B es
  set sls := (HvdH.slices A m B es).flatten with hsls
  have hlen_sls : sls.length = A * m * B := by rw [hsls]; exact hSflat
  have hmem : ∀ x ∈ sls, vsz x ≤ L := by
    intro x hx
    rw [hsls] at hx
    exact hv x (memFlattenSlices A m B es hlen hx)
  refine ⟨hmem, ?_, ?_⟩
  · -- the whole flattened list
    have h1 : vsz (ofList sls) ≤ (sls.length + 1) * (L + 1) := vsz_ofList_le hmem
    rw [hlen_sls] at h1
    exact le_trans h1 (chunkArith A m B N L hm hAmB).1
  · -- its consecutive `m`-chunks
    set chunks := (List.range (sls.length / m)).map
        (fun i => ofList ((sls.drop (i * m)).take m)) with hchunks
    have hdiv : sls.length / m = A * B := by
      rw [hlen_sls, show A * m * B = m * (A * B) by ring]
      exact Nat.mul_div_right (A * B) hm
    have hchunklen : chunks.length = A * B := by
      simp [hchunks, hdiv]
    have hchunk : ∀ c ∈ chunks, vsz c ≤ m * L + m + 1 := by
      intro c hc
      rw [hchunks] at hc
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
      have hsub : ∀ x ∈ (sls.drop (i * m)).take m, vsz x ≤ L := by
        intro x hx
        exact hmem x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
      have h1 : vsz (ofList ((sls.drop (i * m)).take m))
          ≤ ((sls.drop (i * m)).take m).length * L + ((sls.drop (i * m)).take m).length + 1 :=
        vsz_ofList_le_mul hsub
      have h2 : ((sls.drop (i * m)).take m).length ≤ m := by
        rw [List.length_take]; exact Nat.min_le_left _ _
      have h3 : ((sls.drop (i * m)).take m).length * L ≤ m * L :=
        Nat.mul_le_mul_right L h2
      omega
    have h4 : vsz (ofList chunks) ≤ chunks.length * (m * L + m + 1) + chunks.length + 1 :=
      vsz_ofList_le_mul hchunk
    rw [hchunklen] at h4
    exact le_trans h4 (chunkArith A m B N L hm hAmB).2

end Work.SB.BW2
