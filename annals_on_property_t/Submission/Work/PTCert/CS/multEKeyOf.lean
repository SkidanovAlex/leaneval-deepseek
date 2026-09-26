import Mathlib
import Submission.Work.PTCert.CSAux
import Submission.Work.PTCert.cert1Aux

/-!
# Multiplicities of the group keys of the rank-5 certificate

The multiplicity `multE (keyOf r g)` of the group key `(r, g) = 2048 * r + g` is the product of the
row count `cntL.getD r 0` of the row `r` and the size `sizeE r g` of the group `g` of that row.

The data (`multT`, `cntL`, `sizes*`) is opaque; the content is the kernel check
`C.mult_ok{r} : multOK multT r cntr sizes{r} = true`, which says that the packed field
`pget multT 32 (2^32 - 1) (2048 * r + g)` of the multiplicity tree equals `cntr * sizes{g}` for every
`g < sizes{r}.length`, together with `cntr = cntL.getD r 0` and `sizes{r}.length = ngE r`.
-/

namespace Work.PTCert.CS

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.C

/-- The meaning of the kernel check `multOK`: the multiplicity stored in `multT` for the key
`2048 * r + g` is `cntr * sizes{g}`, for every `g < sizes.length`. -/
theorem multOK_sound {r cntr : ℕ} {sizes : List ℕ} (h : multOK multT r cntr sizes = true) :
    ∀ g < sizes.length, pget multT 32 4294967295 (2048 * r + g) = cntr * sizes.getD g 0 := by
  intro g hg
  have h1 := (Work.PTCert.allIdx_iff_CSAux sizes
      (fun g sz => Nat.beq (pget multT 32 4294967295 (2048 * r + g)) (cntr * sz)) 0).mp h
  have h2 := h1 g hg
  rw [Nat.beq_eq, Nat.zero_add] at h2
  rw [h2, List.getD_eq_getElem sizes 0 (n := g) hg]

/-- One row of the multiplicity identity: given the kernel check of the row, the value `cntr` of the
row count and the length of the size list, the identity holds for all groups of the row. -/
theorem row_step {r cntr : ℕ} {sizes : List ℕ}
    (hm : multOK multT r cntr sizes = true) (hsz : sizesL.getD r [] = sizes)
    (hlen : sizes.length = ngE r) (hcnt : cntL.getD r 0 = cntr) :
    ∀ g < ngE r, multE (keyOf r g) = cntL.getD r 0 * sizeE r g := by
  intro g hg
  show pget multT 32 4294967295 (2048 * r + g) = cntL.getD r 0 * (sizesL.getD r []).getD g 0
  rw [hcnt, hsz]
  exact multOK_sound hm g (by rw [hlen]; exact hg)

theorem multEKeyOf : ∀ r < 18, ∀ g < Submission.PTCert.G.ngE r,
    Submission.PTCert.G.multE (Submission.PTCert.G.keyOf r g) =
      Submission.PTCert.D.cntL.getD r 0 * Submission.PTCert.G.sizeE r g := by
  intro r hr
  interval_cases r
  · exact row_step C.mult_ok0 rfl (by decide +kernel) (by decide +kernel)
  · exact row_step C.mult_ok1 rfl (by decide +kernel) (by decide +kernel)
  · exact row_step C.mult_ok2 rfl (by decide +kernel) (by decide +kernel)
  · exact row_step C.mult_ok3 rfl (by decide +kernel) (by decide +kernel)
  · exact row_step C.mult_ok4 rfl (by decide +kernel) (by decide +kernel)
  · exact row_step C.mult_ok5 rfl (by decide +kernel) (by decide +kernel)
  · exact row_step C.mult_ok6 rfl (by decide +kernel) (by decide +kernel)
  · exact row_step C.mult_ok7 rfl (by decide +kernel) (by decide +kernel)
  · exact row_step C.mult_ok8 rfl (by decide +kernel) (by decide +kernel)
  · exact row_step C.mult_ok9 rfl (by decide +kernel) (by decide +kernel)
  · exact row_step C.mult_ok10 rfl (by decide +kernel) (by decide +kernel)
  · exact row_step C.mult_ok11 rfl (by decide +kernel) (by decide +kernel)
  · exact row_step C.mult_ok12 rfl (by decide +kernel) (by decide +kernel)
  · exact row_step C.mult_ok13 rfl (by decide +kernel) (by decide +kernel)
  · exact row_step C.mult_ok14 rfl (by decide +kernel) (by decide +kernel)
  · exact row_step C.mult_ok15 rfl (by decide +kernel) (by decide +kernel)
  · exact row_step C.mult_ok16 rfl (by decide +kernel) (by decide +kernel)
  · exact row_step C.mult_ok17 rfl (by decide +kernel) (by decide +kernel)

end Work.PTCert.CS
