import Mathlib
import Submission.Work.IntLib.chunkDefs

namespace Work.IntLib

/-- The `k`-th step of the `chunk` loop: extending the push order after `k` bit positions by the
next bit of `ps` agrees with the closed form `outOrder`-style block description.  Concretely, for
`k < ps.length` the push sequence produced by the loop is the leading `[cons, pos]` marker of the
current group, followed by the bits of the group read off from `ps`. -/
theorem partBlk_marker_step (ps : List Bool) (b k : ℕ) (hb : 1 ≤ b) (hk : k < ps.length) : (if k % b = 0 then [] else Work.IntLib.partBlk ps b k) ++ (if k % b = 0 then [HvdH.Glyph.cons, HvdH.Glyph.pos] else []) ++ [HvdH.Glyph.bit (ps.getD k false)] = [HvdH.Glyph.cons, HvdH.Glyph.pos] ++ ((ps.drop (b * (k / b))).take (k % b + 1)).map HvdH.Glyph.bit := by
  unfold partBlk
  by_cases h : k % b = 0
  · -- start of a new group: `k = b * (k / b)`, the new bit is the first bit of the group
    have hidx : b * (k / b) = k := by
      have hh := Nat.div_add_mod k b; rw [h, Nat.add_zero] at hh; exact hh
    have htake : (ps.drop (b * (k / b))).take (k % b + 1) = [ps.getD k false] := by
      rw [hidx, h, List.drop_eq_getElem_cons (l := ps) hk,
          List.getD_eq_getElem (l := ps) (d := false) (n := k) hk]
      rfl
    rw [if_pos h, if_pos h, List.nil_append, htake, List.map_cons, List.map_nil]
  · -- inside a group: the next bit extends the run of bits already pushed
    have hidx : b * (k / b) + k % b = k := Nat.div_add_mod k b
    have hlen : k % b < (ps.drop (b * (k / b))).length := by
      simp only [List.length_drop]; omega
    have hget : (ps.drop (b * (k / b)))[k % b] = ps.getD k false := by
      rw [List.getElem_drop (h := hlen), List.getD_eq_getElem (l := ps) (d := false) (n := k) hk]
      simp only [hidx]
    have key : ((ps.drop (b * (k / b))).take (k % b + 1)).map HvdH.Glyph.bit =
        ((ps.drop (b * (k / b))).take (k % b)).map HvdH.Glyph.bit ++ [HvdH.Glyph.bit (ps.getD k false)] := by
      rw [← List.take_concat_get' _ _ hlen, List.map_append, List.map_cons, List.map_nil, hget]
    rw [if_neg h, if_neg h, List.append_nil, key, List.append_assoc]

end Work.IntLib
