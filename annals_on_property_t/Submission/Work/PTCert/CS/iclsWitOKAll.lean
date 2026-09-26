import Mathlib
import Submission.Work.PTCert.CSAux

/-!
# `iclsWitOKAll`: class witnesses for the inverses of the canonical words

The kernel theorem `C.icl_ok{j}_{i}` checks `iclsOK canonT iclT L = true` on the successive
`750`-element chunks `L = List.range' s n` of `[0, 7229)`.  `iclsOK` is `allL` of the per-index
predicate

`clsWitOK canonT ((unpack4 (kG canonT c)).reverse.map invLk) (w34 iclT c)`,

so the checks give, for every `c` in a chunk, the `clsWitOK` statement with the kernel forms
`unpack4 (kG canonT c)` and `invLk`.  Since `canonW c = unpack4 (kG canonT c)` by definition and
`invLk = invL` (`Work.PTCert.invLk_eq_invL`), this is literally the requested statement; the
chunks cover `[0, ncls)` with `ncls = 7229`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Work.PTCert.CS

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D
open Submission.PTCert.C

/-- One chunk check `iclsOK canonT iclT (List.range' s n) = true` gives the `clsWitOK`
statement for every `c ∈ [s, s+n)`, in the `canonW`/`invL` form used in the target. -/
theorem clsWitOK_of_iclsOK_range {s n : ℕ}
    (h : iclsOK canonT iclT (List.range' s n) = true) {c : ℕ} (hs : s ≤ c) (hc : c < s + n) :
    clsWitOK canonT ((canonW c).reverse.map invL) (w34 iclT c) = true := by
  have hlist : (canonW c).reverse.map invL = (unpack4 (kG canonT c)).reverse.map invLk := by
    rw [show canonW c = unpack4 (kG canonT c) from rfl]
    exact List.map_congr_left (fun k _ => (invLk_eq_invL k).symm)
  rw [hlist]
  exact (allL_iff_CSAux _ _).mp h c (List.mem_range'.mpr ⟨c - s, by omega, by omega⟩)

theorem iclsWitOKAll : ∀ c < Submission.PTCert.G.ncls,
    Submission.PTCert.clsWitOK Submission.PTCert.D.canonT
      ((Submission.PTCert.G.canonW c).reverse.map Submission.PTCert.invL)
      (Submission.PTCert.w34 Submission.PTCert.D.iclT c) = true := by
  intro c hc
  have hc' : c < 7229 := hc
  rcases lt_or_ge c 750 with h | h
  · exact clsWitOK_of_iclsOK_range icl_ok0_0 (by omega) (by omega)
  rcases lt_or_ge c 1500 with h2 | h2
  · exact clsWitOK_of_iclsOK_range icl_ok0_1 (by omega) (by omega)
  rcases lt_or_ge c 2250 with h3 | h3
  · exact clsWitOK_of_iclsOK_range icl_ok1_0 (by omega) (by omega)
  rcases lt_or_ge c 3000 with h4 | h4
  · exact clsWitOK_of_iclsOK_range icl_ok1_1 (by omega) (by omega)
  rcases lt_or_ge c 3750 with h5 | h5
  · exact clsWitOK_of_iclsOK_range icl_ok2_0 (by omega) (by omega)
  rcases lt_or_ge c 4500 with h6 | h6
  · exact clsWitOK_of_iclsOK_range icl_ok2_1 (by omega) (by omega)
  rcases lt_or_ge c 5250 with h7 | h7
  · exact clsWitOK_of_iclsOK_range icl_ok3_0 (by omega) (by omega)
  rcases lt_or_ge c 6000 with h8 | h8
  · exact clsWitOK_of_iclsOK_range icl_ok3_1 (by omega) (by omega)
  rcases lt_or_ge c 6750 with h9 | h9
  · exact clsWitOK_of_iclsOK_range icl_ok4_0 (by omega) (by omega)
  · exact clsWitOK_of_iclsOK_range icl_ok4_1 (by omega) (by omega)

end Work.PTCert.CS
