-- PRIVATE COPY (own namespace, Resample/PB dialect) of `Submission/Work/Layout/buildCost_le.lean`.
-- The declarations have been moved from `Work.Layout`/`Work.Resample` into the
-- dedicated namespace `Work.Resample.PBChunk` (with `buildFrameT`/`chunksOfWordT`
-- renamed to `buildFramePB`/`chunksOfWordPB`) so that this module coexists with
-- every other module of the workspace (in particular with `Layout.Take.*` and with
-- `Work.Layout.AA.Defs`).  The proofs are unchanged.
import Mathlib
import Submission.Work.Resample.PBChunk.chunksOfDefs
import Submission.Work.Resample.PBChunk.chunksArith
namespace Work.Resample.PBChunk

open Work.Layout
open HvdH

set_option autoImplicit false

/-! ## Elementary sums over a list of chunks

`buildCost_le` is the cost estimate for `buildProg`: the cost of building the chunk list is
`40 * Σ_c vsz(c) + 80 * m * #ch + 129 * #ch + 7`, and the size of the resulting value is
`vsz (ofList (ch.map ofList))`, which by `vsz_map_ofList_eq` is at least `Σ_c vsz(c) + m * #ch`.
The three lemmas below are the two bookkeeping identities and the final arithmetic. -/

/-- Sum of an affine function of a list: `Σ (a * g x + b) = a * Σ g x + b * #l`. -/
theorem sum_map_affine {α : Type} (l : List α) (g : α → ℕ) (a b : ℕ) :
    (l.map (fun x => a * g x + b)).sum = a * (l.map g).sum + b * l.length := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- Every chunk of `ch` has length `m`, so the total length is `m * ch.length`. -/
theorem sum_map_length_eq (ch : List (List Val)) (m : ℕ) (hlen : ∀ c ∈ ch, c.length = m) :
    (ch.map fun c => c.length).sum = m * ch.length := by
  induction ch with
  | nil => simp
  | cons C ch ih =>
      have hC : C.length = m := hlen C (List.mem_cons_self ..)
      have ih' := ih (fun c hc => hlen c (List.mem_cons_of_mem C hc))
      simp only [List.map_cons, List.sum_cons, List.length_cons, hC, ih']
      ring

/-- Cost of `buildProg` is linear (with constant `40`, `80`, `129`) in the total number of glyphs
moved, the chunk length `m` and the number of chunks; the size of the built list dominates all
three. -/
theorem buildCost_le (ch : List (List HvdH.Val)) (m : ℕ)
    (hlen : ∀ c ∈ ch, c.length = m) :
    (ch.map (fun c => 40 * ((c.map HvdH.vsz).sum) + 80 * m + 129)).sum + 7 ≤
      100 * (HvdH.vsz (HvdH.ofList (ch.map HvdH.ofList)) + ch.length + 1) := by
  have hS : (ch.map (fun c => 40 * (c.map vsz).sum + 80 * m + 129)).sum
      = 40 * (ch.map (fun c => (c.map vsz).sum)).sum + (80 * m + 129) * ch.length :=
    sum_map_affine ch (fun c => (c.map vsz).sum) 40 (80 * m + 129)
  have hlen_sum := sum_map_length_eq ch m hlen
  have hT : vsz (ofList (ch.map ofList))
      = (ch.map (fun c => (c.map vsz).sum)).sum + m * ch.length + 2 * ch.length + 1 := by
    rw [vsz_map_ofList_eq, sum_map_add', hlen_sum]
  rw [hS, hT]
  nlinarith [Nat.zero_le ((ch.map (fun c => (c.map vsz).sum)).sum), Nat.zero_le m,
    Nat.zero_le ch.length, Nat.zero_le (m * ch.length)]

end Work.Resample.PBChunk