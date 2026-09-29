import Mathlib
import Submission.Work.Transform.phiAux

set_option autoImplicit false

namespace Work.Transform

open HvdH

/-- `getD` of a `map` over `List.range` at an index in range. -/
private theorem getD_map_range {α : Type} [Inhabited α] {N i : ℕ} (g : ℕ → α) (hi : i < N) :
    ((List.range N).map g).getD i (default : α) = g i := by
  have h1 : i < ((List.range N).map g).length := by simpa using hi
  rw [List.getD_eq_getElem (l := (List.range N).map g) (d := (default : α)) h1, List.getElem_map,
    List.getElem_range]

/-- Read a list of values back as a list of fixed-point pairs: if `zs : List Val` has length `N`
and every entry is a `cfxVal`, then there is `c : List (ℤ × ℤ)` with `zs = c.map cfxVal` (i.e.
`ofList zs = cvecVal c`), `c.length = N`, and every property `Q i w` that comes with the `i`-th
entry transfers to `c.getD i (0,0)`.  For use with `KernelLib.zipWith` output lists.
Proof sketch: `classical`; `c := (List.range N).map fun i => if h : i < N then Classical.choose
(hex i h) else 0`, then compare `zs` and `c.map cfxVal` indexwise with `List.ext_getElem`,
`List.getElem_map`, `List.getElem_range` (`List.getD_eq_getElem` to pass between `getD` and `[·]`);
`cfxVal_injective` (`Submission.Work.Transform.phiAux`) turns the `cfxVal`-equality into the pair
equality.  Guidance: keep auxiliary lemmas `private`. -/
theorem extractCvec {N : ℕ} {zs : List HvdH.Val} {Q : ℕ → ℤ × ℤ → Prop}
    (hlen : zs.length = N)
    (h : ∀ i < N, ∃ w : ℤ × ℤ, zs.getD i HvdH.Val.nil = HvdH.cfxVal w ∧ Q i w) :
    ∃ c : List (ℤ × ℤ), HvdH.ofList zs = HvdH.cvecVal c ∧ c.length = N ∧
      ∀ i < N, Q i (c.getD i (0, 0)) := by
  classical
  -- the `i`-th chosen pair, left as `0` outside the range
  set g : ℕ → ℤ × ℤ := fun i => if hh : i < N then Classical.choose (h i hh) else 0 with hg
  have hg_spec : ∀ i (hi : i < N), zs.getD i Val.nil = cfxVal (g i) ∧ Q i (g i) := by
    intro i hi
    have hgi : g i = Classical.choose (h i hi) := by
      rw [hg]
      exact dite_eq_left hi
    rw [hgi]
    exact Classical.choose_spec (h i hi)
  set c : List (ℤ × ℤ) := (List.range N).map g with hc
  have hc_len : c.length = N := by simp [hc]
  have hc_get : ∀ i, i < N → c.getD i (0, 0) = g i := by
    intro i hi
    rw [hc]
    exact getD_map_range g hi
  have hcmap_get : ∀ i, i < N → (c.map cfxVal).getD i Val.nil = cfxVal (g i) := by
    intro i hi
    have hi' : i < c.length := by rw [hc_len]; exact hi
    have h1 : i < (c.map cfxVal).length := by rw [List.length_map, hc_len]; exact hi
    rw [List.getD_eq_getElem (l := c.map cfxVal) (d := Val.nil) h1, List.getElem_map,
      ← List.getD_eq_getElem (l := c) (d := ((0, 0) : ℤ × ℤ)) hi', hc_get i hi]
  have hzeq : zs = c.map cfxVal := by
    refine List.ext_getElem ?_ ?_
    · rw [List.length_map, hc_len, hlen]
    · intro i h1 h2
      have h1N : i < N := by rw [← hlen]; exact h1
      rw [← List.getD_eq_getElem (l := zs) (d := Val.nil) h1,
        ← List.getD_eq_getElem (l := c.map cfxVal) (d := Val.nil) h2,
        (hg_spec i h1N).1, hcmap_get i h1N]
  refine ⟨c, ?_, hc_len, ?_⟩
  · rw [hzeq]
    rfl
  · intro i hi
    rw [hc_get i hi]
    exact (hg_spec i hi).2

end Work.Transform
