import Mathlib
import Submission.Work.Resample.buQWdefs

/-!
# `Work.Resample.buQWSelDefs`: the objects of the selection stage of the `B̃` word

The stage `buQWsel` of `Work.Resample.buQW` reads the input vector `u` (length `t`) together with
the static key list `buKeysT s t` and the parameter `s`, and produces

`buSelL s t u = (fun ℓ : Fin s => buHalve (u.getD (egNu s t ℓ) (0,0)))`

(paper Prop. 4.7(ii): the fused `C̃ ∘ P̃_t` selection followed by the halving).

The word is `zipWith` (`KL.consV`) of the key list with the vector, then `LL.sortByKey`, then
`LL.take s`, then `KL.mapList` with the element word that drops the key and halves the pair.

This module fixes the list-level objects those stages mention, so that the stage lemmas can be
stated without repeating the (unwieldy) `zip`/`ofFn` expressions.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- The key list of the fused `C̃ ∘ P̃_t` step, as a list of `Val`s: the `i`-th entry is the
destination key `egLam s t i` of the source element `i < t`. -/
noncomputable def buSelKeys (s t : ℕ) : List Val :=
  (List.ofFn (fun i : Fin t => ((egLam s t (i : ℕ) : ℕ) : ℤ))).map Val.int

/-- `buKeysT s t` (the 7-th entry of the static table) is `ofList (buSelKeys s t)`. -/
theorem buKeysT_eq (s t : ℕ) : buKeysT s t = ofList (buSelKeys s t) := rfl

/-- The list of keyed records `cons (int (egLam s t i)) (cfxVal (uᵢ))`, `i < t`, in the *input*
order; this is what the `zipWith` stage produces. -/
noncomputable def buSelRecs (s t : ℕ) (u : List (ℤ × ℤ)) : List Val :=
  ((buSelKeys s t).zip (u.map cfxVal)).map (fun p : Val × Val => Val.cons p.1 p.2)

/-- The same list of records in `ofFn` form (the form the sort is analysed in). -/
noncomputable def buSelRecs' (s t : ℕ) (u : List (ℤ × ℤ)) : List Val :=
  List.ofFn (fun i : Fin t =>
    Val.cons (Val.int (((egLam s t (i : ℕ) : ℕ) : ℤ))) (cfxVal (u.getD (i : ℕ) (0, 0))))

/-- The element map of the selection: drop the key, halve the fixed-point pair. -/
def buSelElem : Val → Val
  | Val.cons (Val.int _) (Val.cons (Val.int x) (Val.int y)) =>
      Val.cons (Val.int (Int.tdiv x 2)) (Val.int (Int.tdiv y 2))
  | _ => Val.nil

theorem buSelElem_apply (k : ℤ) (z : ℤ × ℤ) :
    buSelElem (Val.cons (Val.int k) (cfxVal z)) = cfxVal (buHalve z) := rfl

/-- The inverse of `cfxVal` on a pair value (`(0,0)` elsewhere). -/
def buUnCfx : Val → ℤ × ℤ
  | Val.cons (Val.int x) (Val.int y) => (x, y)
  | _ => (0, 0)

theorem buUnCfx_cfxVal (z : ℤ × ℤ) : buUnCfx (cfxVal z) = z := rfl

/-- The pair vector extracted from a list of pair values. -/
def buUnCfxL (l : List Val) : List (ℤ × ℤ) := l.map buUnCfx

theorem buUnCfxL_cfxVal (l : List (ℤ × ℤ)) : buUnCfxL (l.map cfxVal) = l := by
  rw [buUnCfxL, List.map_map]
  have h : (buUnCfx ∘ cfxVal) = id := funext buUnCfx_cfxVal
  rw [h, List.map_id]

end Work.Resample
