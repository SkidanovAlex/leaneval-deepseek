-- PRIVATE COPY (own namespace, Resample/PB dialect) of `Submission/Work/Layout/chunk_len_mul_le_sum_vsz.lean`.
-- The declarations have been moved from `Work.Layout`/`Work.Resample` into the
-- dedicated namespace `Work.Resample.PBChunk` (with `buildFrameT`/`chunksOfWordT`
-- renamed to `buildFramePB`/`chunksOfWordPB`) so that this module coexists with
-- every other module of the workspace (in particular with `Layout.Take.*` and with
-- `Work.Layout.AA.Defs`).  The proofs are unchanged.
import Mathlib
import Submission.Work.Resample.PBChunk.chunksOfDefs
namespace Work.Resample.PBChunk

open Work.Layout
/-- If every chunk of `ch` has length `m`, then the total number of values `m * ch.length`
is dominated by the sum of the values' sizes: each value contributes at least one glyph. -/
theorem chunk_len_mul_le_sum_vsz (ch : List (List HvdH.Val)) (m : ℕ)
    (hlen : ∀ c ∈ ch, c.length = m) :
    m * ch.length ≤ (ch.map (fun c => (c.map HvdH.vsz).sum)).sum := by
  induction ch generalizing m with
  | nil => simp
  | cons c ch ih =>
    have hc : c.length = m := hlen c (by simp)
    have hsum : m ≤ (c.map HvdH.vsz).sum := by
      have h1 : ∀ v ∈ c.map HvdH.vsz, 1 ≤ v := by
        intro v hv
        obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv
        exact one_le_vsz w
      have h2 := List.length_le_sum_of_one_le (c.map HvdH.vsz) h1
      rwa [List.length_map, hc] at h2
    have hih := ih m (fun c' h => hlen c' (by simp [h]))
    rw [List.length_cons, List.map_cons, List.sum_cons, Nat.mul_succ]
    omega

end Work.Resample.PBChunk