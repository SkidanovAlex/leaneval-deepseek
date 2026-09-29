import Mathlib
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.Layout.AA.Defs

namespace Work.Layout.AA

/-- The encoding of a nonnegative integer value `Val.int (k : ℤ)` splits as
`D ++ [Glyph.iend]`, where `D` is the sign glyph `pos` followed by the bits of `k` (least
significant first).  The digits `D` contain neither the terminator `iend` nor the free marker
`mk 7`, and `D.length + 1 = isz k`. -/
theorem enc_int_decomp (k : ℕ) :
    ∃ D : List HvdH.Glyph,
      (HvdH.Val.int (k : ℤ)).enc = D ++ [HvdH.Glyph.iend] ∧
      HvdH.Glyph.iend ∉ D ∧ HvdH.Glyph.mk 7 ∉ D ∧ D.length + 1 = HvdH.isz (k : ℤ) := by
  refine ⟨HvdH.Glyph.pos :: (Computability.encodeNat k).map HvdH.Glyph.bit, ?_, ?_, ?_, ?_⟩
  · rw [Work.IntLib.enc_int]
    simp
  · intro h
    simp only [List.mem_cons, List.mem_map] at h
    rcases h with h | ⟨b, _, hb⟩
    · exact absurd h (by decide)
    · cases b <;> exact absurd hb (by decide)
  · intro h
    simp only [List.mem_cons, List.mem_map] at h
    rcases h with h | ⟨b, _, hb⟩
    · exact absurd h (by decide)
    · cases b <;> exact absurd hb (by decide)
  · simp only [List.length_cons, List.length_map, Work.IntLib.encodeNat_length,
      Work.IntLib.isz_eq, Int.natAbs_natCast]

end Work.Layout.AA
