import Mathlib
import Submission.Work.KronP.kdefs
import Submission.Work.IntLib.chunksAPI

/-!
# `HvdH.chunks` inverts `HvdH.evalChunks`

`HvdH.chunks x b N` is the list of the `N` base-`2^b` digits of `x` (least significant first) and
`HvdH.evalChunks hs b = Σ_j hs[j]·2^{b j}`.  This file proves that the two operations are inverse
to each other on lists whose entries all fit in one digit: if `d` has length `N` and every entry of
`d` is `< 2^w` then `chunks (evalChunks d w) w N = d`.

The proof goes through Mathlib's `Nat.digitsAppend` (the base-`b` digits of `n`, zero-padded to a
fixed length), for which `Nat.setInvOn_digitsAppend_ofDigits` says that `Nat.ofDigits b` and
`b.digitsAppend l` are mutually inverse between `{n | n < b^l}` and the length-`l` lists with
entries `< b`.
-/

set_option autoImplicit false

namespace Work.KronP

open HvdH

/-- For `x < (2^w)^N`, the `N` base-`2^w` digits of `x` are the zero-padded base-`2^w` digits of
`x`. -/
theorem chunks_eq_digitsAppend {w : ℕ} (hw : 1 ≤ w) {x N : ℕ} (hx : x < (2^w)^N) :
    HvdH.chunks x w N = Nat.digitsAppend (2^w) N x := by
  have hb : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hpow : 2 ^ (w * N) = (2 ^ w) ^ N := by rw [pow_mul]
  have hmod : x % (2 ^ w) ^ N = x := Nat.mod_eq_of_lt hx
  have hlen2 : (Nat.digitsAppend (2 ^ w) N x).length = N := Nat.length_digitsAppend hb N hx
  have hlen : (HvdH.chunks x w N).length = (Nat.digitsAppend (2 ^ w) N x).length := by
    rw [Work.IntLib.chunks_length, hlen2]
  refine Nat.ofDigits_inj_of_len_eq hb hlen ?_ ?_ ?_
  · intro a ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    exact Nat.mod_lt _ (Nat.two_pow_pos w)
  · intro a ha
    exact Nat.lt_of_mem_digitsAppend hb N a ha
  · rw [← Work.IntLib.evalChunks_eq_ofDigits, Work.IntLib.evalChunks_chunks, hpow, hmod]
    exact ((Nat.setInvOn_digitsAppend_ofDigits hb N).2 hx).symm

/-- `HvdH.evalChunks` is a left inverse of `HvdH.chunks`: for `x < 2^(b*N)`, reading back the `N`
base-`2^b` digits of `x` recovers `x`. -/
theorem evalChunks_chunks_of_lt {x b N : ℕ} (hx : x < 2 ^ (b * N)) :
    HvdH.evalChunks (HvdH.chunks x b N) b = x := by
  rw [Work.IntLib.evalChunks_chunks, Nat.mod_eq_of_lt hx]

theorem chunksDigits {w : ℕ} (hw : 1 ≤ w) (d : List ℕ) (hbd : ∀ x ∈ d, x < 2 ^ w)
    {N : ℕ} (hN : d.length = N) :
    HvdH.chunks (HvdH.evalChunks d w) w N = d := by
  have hb : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hx : HvdH.evalChunks d w < (2^w)^N := by
    rw [Work.IntLib.evalChunks_eq_ofDigits, ← hN]
    exact Nat.ofDigits_lt_base_pow_length hb hbd
  rw [chunks_eq_digitsAppend hw hx]
  have h1 := (Nat.setInvOn_digitsAppend_ofDigits hb N).1 ⟨hN, hbd⟩
  rwa [← Work.IntLib.evalChunks_eq_ofDigits] at h1

end Work.KronP
