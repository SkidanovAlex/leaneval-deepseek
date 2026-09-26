import Mathlib
import Submission.Work.PTCert.Glue3
import Submission.Work.PTCert.actCSound
import Submission.Work.PTCert.sigmaGroupFacts
import Submission.Work.PTCert.lprodProdImg

/-!
# `PTCert.OrbitKeys` — helper definitions and small bridge lemmas

Small bridge definitions/lemmas for the orbit decomposition `Work.PTCert.orbitKeys`
(`Submission/Work/PTCert/orbitKeys.lean`): the element of `EI` with code `grepE r g`, its value,
and the identification of `fE` on the row/group representatives with `eltC` of the codes.

Nothing here unfolds the big data except through the semantic `Prop`s (`RowSem`, `GroupSem`).
-/

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D
open scoped BigOperators

set_option autoImplicit false

noncomputable section

namespace Work.PTCert.OrbitKeys

/-- The element of `EI` whose code is `grepE r g` (the base point `pt0` if that is not a code
of `B₂`). -/
def grepEI (r g : ℕ) : EI := toEI (grepE r g) pt0

/-- Membership in the list `eAll` gives membership in `eS = eAll.toFinset`. -/
lemma mem_eS_of_mem (z : ℕ) (h : z ∈ eAll) : z ∈ eS := List.mem_toFinset.mpr h

/-- Membership in `eS` is membership in the list `eAll`. -/
lemma mem_eS_iff (z : ℕ) : z ∈ eS ↔ z ∈ eAll := List.mem_toFinset

/-- The value of `toEI z x` when `z` is a code. -/
lemma toEI_val {z : ℕ} (x : EI) (h : z ∈ eS) : (toEI z x).1 = z := by
  rw [toEI, dif_pos h]

/-- `toEI z x` when `z` is a code. -/
lemma toEI_eq {z : ℕ} (x : EI) (h : z ∈ eS) : toEI z x = ⟨z, h⟩ := by
  rw [toEI, dif_pos h]

/-- The code of the row representative `x0E r pt0` is `x0c r`. -/
lemma x0E_val (hR : RowSem) {r : ℕ} (hr : r < 18) : (x0E r pt0).1 = x0c r :=
  toEI_val pt0 (mem_eS_of_mem _ (hR.2.1 r hr))

/-- The code of `grepEI r g` is `grepE r g`. -/
lemma grepEI_val {r g : ℕ} (h : grepE r g ∈ eS) : (grepEI r g).1 = grepE r g :=
  toEI_val pt0 h

/-- `fE` of the row representative is `eltC` of its code. -/
lemma fE_x0E (hR : RowSem) {r : ℕ} (hr : r < 18) : fE (x0E r pt0) = eltC (x0c r) := by
  show eltC (toEI (x0c r) pt0).1 = eltC (x0c r)
  rw [toEI_val pt0 (mem_eS_of_mem _ (hR.2.1 r hr))]

/-- `fE` of the group representative is `eltC` of its code. -/
lemma fE_grepEI {r g : ℕ} (h : grepE r g ∈ eS) : fE (grepEI r g) = eltC (grepE r g) := by
  show eltC (toEI (grepE r g) pt0).1 = eltC (grepE r g)
  rw [toEI_val pt0 h]

/-- `fE` of the base point (the identity of the group) is `1`. -/
lemma fE_x0E_zero (hR : RowSem) : fE (x0E 0 pt0) = 1 := by
  rw [fE_x0E hR (by norm_num), hR.1, Work.PTCert.eltC_zero]

/-- Codes of `grepE r g` are codes of `B₂` (rows `r ≥ 1`). -/
lemma grepE_mem_pos (hG : GroupSem) {r g : ℕ} (hr : r < 18) (hr1 : 1 ≤ r) (hg : g < ngE r) :
    grepE r g ∈ eS :=
  mem_eS_of_mem _ ((hG.2.2 r hr hr1).2.1 g hg).1

/-- Codes of `grepE 0 g` are codes of `B₂` (row `0`: the groups are the rows). -/
lemma grepE_mem_zero (hG : GroupSem) (hR : RowSem) {g : ℕ} (hg : g < ngE 0) :
    grepE 0 g ∈ eS := by
  have hg18 : g < 18 := by rw [← hG.1]; exact hg
  rw [hG.2.1 g hg18]
  exact mem_eS_of_mem _ (hR.2.1 g hg18)

end Work.PTCert.OrbitKeys

end
