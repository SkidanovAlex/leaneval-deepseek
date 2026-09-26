import Mathlib
import Submission.Work.PTCert.eAux

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.C

/-- `eAll` is closed under the normal form of a product of two letters `< 81`.
Recipe: from the three checks `Submission.PTCert.C.ecompl_ok0/1/2`
(`eCompleteOK cmT eM [0..26]`, `[27..53]`, `[54..80]`), `Work.PTCert.allL_iff_eAux`, `Work.PTCert.allR_iff_eAux`,
`Work.PTCert.allL_append_eAux` and the `rfl`-fact `[0..26] ++ [27..53] ++ [54..80] = List.range 81`
get, for every `a < 81` and `b < 81`, `em (normC cmT a b) ≠ 0`; combine with
`Work.PTCert.normC_lt` (giving `normC cmT a b < 10368`, for `a,b < 81`) and the hypothesis
`hmem` (the membership characterisation proved in `PTCert/eExactFacts`). -/
theorem eClosure
    (hmem : ∀ z < 10368, z ∈ Submission.PTCert.D.eAll ↔ Submission.PTCert.G.em z ≠ 0) :
    ∀ a < 81, ∀ b < 81,
      Submission.PTCert.normC Submission.PTCert.D.cmT a b ∈ Submission.PTCert.D.eAll := by
  -- The three `eCompleteOK` checks, transcribed into the `allL` form.
  have h0 : allL
      [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26]
      (fun a => allR 81 (fun b => !(Nat.beq (eG eM (normC cmT a b)) 0))) = true :=
    ecompl_ok0
  have h1 : allL
      [27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53]
      (fun a => allR 81 (fun b => !(Nat.beq (eG eM (normC cmT a b)) 0))) = true :=
    ecompl_ok1
  have h2 : allL
      [54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80]
      (fun a => allR 81 (fun b => !(Nat.beq (eG eM (normC cmT a b)) 0))) = true :=
    ecompl_ok2
  -- The conjunction of the three checks, on the concatenated list.
  have hla : allL
      ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26] ++
       [27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53] ++
       [54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80] : List ℕ)
      (fun a => allR 81 (fun b => !(Nat.beq (eG eM (normC cmT a b)) 0))) = true := by
    rw [allL_append_eAux, allL_append_eAux, h0, h1, h2]
    rfl
  -- The concatenation is exactly `List.range 81`.
  have hrange :
      ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26] ++
       [27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53] ++
       [54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80] : List ℕ)
      = List.range 81 := rfl
  intro a ha b hb
  -- `a` lies in the concatenated list, so the `allR 81` block at row `a` is `true`.
  have hrow : allR 81 (fun b => !(Nat.beq (eG eM (normC cmT a b)) 0)) = true :=
    (allL_iff_eAux _ _).mp hla a (by rw [hrange]; exact List.mem_range.mpr ha)
  -- Reading off the `b`-th entry gives `em (normC cmT a b) ≠ 0`.
  have hb' : (!(Nat.beq (eG eM (normC cmT a b)) 0)) = true :=
    (allR_iff_eAux 81 _).mp hrow b hb
  have hbne : eG eM (normC cmT a b) ≠ 0 := by
    intro hz
    rw [hz, Nat.beq_refl] at hb'
    exact Bool.false_ne_true hb'
  -- Convert to membership via the characterisation `hmem`.
  exact (hmem (normC cmT a b) (normC_lt cmT a b ha hb)).mpr hbne

end Work.PTCert
