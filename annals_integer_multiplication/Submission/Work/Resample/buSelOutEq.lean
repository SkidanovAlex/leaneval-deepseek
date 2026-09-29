import Mathlib
import Submission.Work.Resample.buQWSelDefs

/-!
# `Work.Resample.buSelOutEq`: the output list of the selection stage

The selection stage of the `B̃` word (`Work.Resample.buQWsel`) takes the vector `u` (length `t`),
sorts the keyed records `cons (int (egLam s t i)) (cfxVal uᵢ)` (`i < t`) by destination key and
keeps the first `s` of them; then it applies the element word `buSelElem` (drop the key, halve the
pair) to each.  This module proves the pure list-arithmetic bookkeeping step: if `ys` is any list of
values whose `ℓ`-th entry is the record with key `ℓ` and payload `u (egNu s t ℓ)` (`ℓ < s`), then
mapping `buSelElem` over its first `s` entries gives exactly `buSelL s t u` (paper Prop. 4.7(ii),
the fused `C̃ ∘ P̃_t`).
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

theorem buSelOutEq (s t : ℕ) (hst : s < t) (u : List (ℤ × ℤ)) (hu : u.length = t) (ys : List HvdH.Val)
    (hlen : ys.length = t)
    (hget : ∀ ℓ < s, ys.getD ℓ HvdH.Val.nil =
      HvdH.Val.cons (HvdH.Val.int (ℓ : ℤ)) (HvdH.cfxVal (u.getD (Work.Resample.egNu s t ℓ) (0, 0)))) :
    (ys.take s).map Work.Resample.buSelElem = (Work.Resample.buSelL s t u).map HvdH.cfxVal := by
  have htake_len : (ys.take s).length = s := by
    rw [List.length_take, hlen, Nat.min_eq_left (le_of_lt hst)]
  -- The left-hand side, entry by entry (`buSelElem` on the `ℓ`-th record).
  have h1 : (ys.take s).map Work.Resample.buSelElem
      = List.ofFn (fun ℓ : Fin s => HvdH.cfxVal (Work.Resample.buHalve
          (u.getD (Work.Resample.egNu s t (ℓ : ℕ)) (0, 0)))) := by
    apply List.ext_getElem
    · rw [List.length_map, htake_len, List.length_ofFn]
    · intro i hi1 hi2
      rw [List.getElem_map, List.getElem_ofFn hi2]
      have hi_s : i < s := by
        have hlt : i < (ys.take s).length := by simpa [List.length_map] using hi1
        rwa [htake_len] at hlt
      have hi_ys : i < ys.length := by rw [hlen]; omega
      have hysi : ys[i] = ys.getD i HvdH.Val.nil := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_ys]
        simp
      rw [List.getElem_take, hysi, hget i hi_s]
      exact Work.Resample.buSelElem_apply (i : ℤ) (u.getD (Work.Resample.egNu s t i) (0, 0))
  -- The right-hand side, entry by entry (`buSelL` is the `ofFn` of the halved selection).
  have h2 : (Work.Resample.buSelL s t u).map HvdH.cfxVal
      = List.ofFn (fun ℓ : Fin s => HvdH.cfxVal (Work.Resample.buHalve
          (u.getD (Work.Resample.egNu s t (ℓ : ℕ)) (0, 0)))) := by
    rw [Work.Resample.buSelL, List.map_ofFn]
    rfl
  rw [h1, h2]

end Work.Resample
