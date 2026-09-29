import Mathlib
import Submission.Work.IntLib.evEmitDefs

/-!
# `IntLib` / `evEmit`: the value phase

`evValProg` (see `Submission/Work/IntLib/evEmitDefs.lean`) turns the window `W` (stack `aW`) and the
finalised low bits `LO` (stack `aO`, most significant bit first, below the sign `pos`) into the
encoding of `V = ofBits LO + 2^(LO.length) * ofBits W` on the scratch stack `evS2`, written as
`(V.bits.map bit).reverse ++ [pos]` above the frame marker `Shift.gmk evS2`.

The program is

* `pushConst evS2 pos`: push the sign on `evS2`;
* `drainUntil aO evS1 pos`: move the bits of `LO` onto `evS1` (reversing them), dropping the sign;
* `pop aO`: discard the marker `Shift.gmk aO` (restoring `aO` to `Y aO`);
* `drainUntil evS1 evS2 (gmk evS1)`: move the bits of `LO` onto `evS2` (reversing them again, so
  they lie most significant first above the sign) and drop the marker of `evS1`;
* `drainUntil aW evS2 (gmk aW)`: move the bits of `W` onto `evS2` (reversing them), so that after
  this step the region above `pos` is `((LO ++ W).map bit).reverse`, whose bits read little-endian
  represent `V`;
* `dropZerosProg evS2`: delete the leading (most significant) `bit false` glyphs, i.e. canonicalise.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

theorem evEmit_vals (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (W LO : List Bool) (V : ℕ) (Y : HvdH.Stk → List HvdH.Glyph)
    (hW : X Work.IntLib.aW = W.map HvdH.Glyph.bit ++ Work.IntLib.Shift.gmk Work.IntLib.aW :: Y Work.IntLib.aW)
    (hO : X Work.IntLib.aO = LO.reverse.map HvdH.Glyph.bit ++ [HvdH.Glyph.pos] ++ Work.IntLib.Shift.gmk Work.IntLib.aO :: Y Work.IntLib.aO)
    (hS1 : X Work.IntLib.evS1 = Work.IntLib.Shift.gmk Work.IntLib.evS1 :: Y Work.IntLib.evS1)
    (hS2 : X Work.IntLib.evS2 = Work.IntLib.Shift.gmk Work.IntLib.evS2 :: Y Work.IntLib.evS2)
    (hVal : Work.IntLib.ofBits LO + 2 ^ LO.length * Work.IntLib.ofBits W = V) :
    ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main Work.IntLib.evValProg ⟨g, X⟩ s' n ∧
      n ≤ 13 * LO.length + 8 * W.length + 25 ∧
      s'.stk Work.IntLib.aO = Y Work.IntLib.aO ∧ s'.stk Work.IntLib.aW = Y Work.IntLib.aW ∧
      s'.stk Work.IntLib.evS1 = Y Work.IntLib.evS1 ∧
      s'.stk Work.IntLib.evS2 = (V.bits.map HvdH.Glyph.bit).reverse ++ [HvdH.Glyph.pos] ++ Work.IntLib.Shift.gmk Work.IntLib.evS2 :: Y Work.IntLib.evS2 ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.aO → j ≠ Work.IntLib.aW → j ≠ Work.IntLib.evS1 → j ≠ Work.IntLib.evS2 → s'.stk j = X j) := by
  -- the initial state, viewed through its stack function
  have hstk0 : ∀ j : Stk, (⟨g, X⟩ : State).stk j = X j := fun j => rfl
  -- the elementary side condition on the drained region of `aO`
  have hne_bit_pos : ∀ h ∈ LO.reverse.map Glyph.bit, h ≠ Glyph.pos := by
    intro h hh
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hh
    cases b <;> decide
  -- step 1: push the sign `pos` on `evS2`
  obtain ⟨s1, n1, hev1, hn1, hs1S2, hs1oth⟩ := ev_pushConst main evS2 Glyph.pos evR ⟨g, X⟩
  have hs1othX : ∀ j : Stk, j ≠ evS2 → s1.stk j = X j := by
    intro j hj
    rw [hs1oth j hj, hstk0 j]
  have hs1aO : s1.stk aO = LO.reverse.map Glyph.bit ++ Glyph.pos :: Shift.gmk aO :: Y aO := by
    rw [hs1othX aO (by decide)]
    simpa only [List.append_assoc, List.singleton_append] using hO
  have hs1aW : s1.stk aW = W.map Glyph.bit ++ Shift.gmk aW :: Y aW := by
    rw [hs1othX aW (by decide)]; exact hW
  have hs1S1 : s1.stk evS1 = Shift.gmk evS1 :: Y evS1 := by
    rw [hs1othX evS1 (by decide)]; exact hS1
  have hs1S2' : s1.stk evS2 = Glyph.pos :: Shift.gmk evS2 :: Y evS2 := by
    rw [hs1S2, hstk0 evS2, hS2]
  -- step 2: drain the bits of `LO` off `aO` onto `evS1` (up to the sign), dropping the sign
  obtain ⟨s2, n2, hev2, hn2, hs2aO, hs2S1, hs2oth⟩ :=
    ev_drainUntil main (k := aO) (k' := evS1) (by decide) (T := Glyph.pos) (r := evR)
      (gs := LO.reverse.map Glyph.bit) (below := Shift.gmk aO :: Y aO) s1 hne_bit_pos hs1aO
  have hs2S1' : s2.stk evS1 = LO.map Glyph.bit ++ Shift.gmk evS1 :: Y evS1 := by
    rw [hs2S1, hs1S1]
    simp only [List.map_reverse, List.reverse_reverse]
  -- step 3: discard the marker of `aO`
  obtain ⟨s3, n3, hev3, hn3, hs3aO, hs3oth⟩ := ev_popHead main aO evR s2
  have hs3aO' : s3.stk aO = Y aO := by
    rw [hs3aO, hs2aO]; rfl
  have hs3S1 : s3.stk evS1 = LO.map Glyph.bit ++ Shift.gmk evS1 :: Y evS1 := by
    rw [hs3oth evS1 (by decide)]; exact hs2S1'
  -- step 4: drain the bits of `LO` off `evS1` onto `evS2` (reversing them so that they now lie most
  -- significant first above the sign), dropping the marker of `evS1`
  obtain ⟨s4, n4, hev4, hn4, hs4S1, hs4S2, hs4oth⟩ :=
    ev_drainUntil main (k := evS1) (k' := evS2) (by decide) (T := Shift.gmk evS1) (r := evR)
      (gs := LO.map Glyph.bit) (below := Y evS1) s3
      (fun h hh => by obtain ⟨b, _, rfl⟩ := List.mem_map.mp hh; exact Shift.bit_ne_gmk evS1 b) hs3S1
  have hs4S2' : s4.stk evS2 = LO.reverse.map Glyph.bit ++ Glyph.pos :: Shift.gmk evS2 :: Y evS2 := by
    rw [hs4S2, hs3oth evS2 (by decide), hs2oth evS2 (by decide) (by decide), hs1S2']
    simp only [List.map_reverse]
  -- step 5: drain the bits of `W` off `aW` onto `evS2`
  have hs4aW : s4.stk aW = W.map Glyph.bit ++ Shift.gmk aW :: Y aW := by
    rw [hs4oth aW (by decide) (by decide), hs3oth aW (by decide),
      hs2oth aW (by decide) (by decide), hs1othX aW (by decide)]
    exact hW
  obtain ⟨s5, n5, hev5, hn5, hs5aW, hs5S2, hs5oth⟩ :=
    ev_drainUntil main (k := aW) (k' := evS2) (by decide) (T := Shift.gmk aW) (r := evR)
      (gs := W.map Glyph.bit) (below := Y aW) s4
      (fun h hh => by obtain ⟨b, _, rfl⟩ := List.mem_map.mp hh; exact Shift.bit_ne_gmk aW b) hs4aW
  have hs5S2' : s5.stk evS2 =
      ((LO ++ W).map Glyph.bit).reverse ++ Glyph.pos :: Shift.gmk evS2 :: Y evS2 := by
    rw [hs5S2, hs4S2']
    simp only [List.map_append, List.reverse_append, List.map_reverse, List.append_assoc]
  -- step 6: strip the leading (most significant) `bit false` glyphs
  obtain ⟨s6, n6, hev6, hn6, hs6S2, hs6oth⟩ :=
    ev_dropZeros main evS2 evR (M := Glyph.pos) (by decide) ((LO ++ W).map Glyph.bit)
      (Shift.gmk evS2 :: Y evS2) s5 hs5S2'
  -- the canonical bit list of `V`
  have hVeq : ofBits (LO ++ W) = V := by
    rw [ofBits_append]; exact hVal
  have hstrip : stripFalses ((LO ++ W).map Glyph.bit) = V.bits.map Glyph.bit := by
    rw [stripFalses_map_bit, hVeq]
  have hs6S2' : s6.stk evS2 =
      (V.bits.map Glyph.bit).reverse ++ Glyph.pos :: Shift.gmk evS2 :: Y evS2 := by
    rw [hs6S2, hstrip]
  -- cost bookkeeping
  have hn2' : n2 ≤ 5 * LO.length + 6 := by
    simpa only [List.length_map, List.length_reverse] using hn2
  have hn4' : n4 ≤ 5 * LO.length + 6 := by
    simpa only [List.length_map] using hn4
  have hn5' : n5 ≤ 5 * W.length + 6 := by
    simpa only [List.length_map] using hn5
  have hn6' : n6 ≤ 3 * ((LO.length + W.length) + 1) + 1 := by
    simpa only [List.length_map, List.length_append] using hn6
  -- assemble the six phases
  have hchain : Work.Layout.Ev main
      (Work.Layout.seqs [pushConst evS2 Glyph.pos evR, drainUntil aO evS1 Glyph.pos evR,
        .pop aO evR, drainUntil evS1 evS2 (Shift.gmk evS1) evR,
        drainUntil aW evS2 (Shift.gmk aW) evR, dropZerosProg evS2 evR])
      ⟨g, X⟩ s6 (n1 + (n2 + (n3 + (n4 + (n5 + n6))))) :=
    Work.Layout.Ev.seqs_cons hev1 (Work.Layout.Ev.seqs_cons hev2
      (Work.Layout.Ev.seqs_cons hev3 (Work.Layout.Ev.seqs_cons hev4
        (Work.Layout.Ev.seqs_cons hev5 hev6))))
  have hEv : Work.Layout.Ev main evValProg ⟨g, X⟩ s6 (n1 + n2 + n3 + n4 + n5 + n6) := by
    rw [evValProg]
    exact hchain.mono (by omega)
  refine ⟨s6, n1 + n2 + n3 + n4 + n5 + n6, hEv, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs6oth aO (by decide), hs5oth aO (by decide) (by decide),
      hs4oth aO (by decide) (by decide), hs3aO']
  · rw [hs6oth aW (by decide), hs5aW]
  · rw [hs6oth evS1 (by decide), hs5oth evS1 (by decide) (by decide), hs4S1]
  · rw [hs6S2']
    simp only [List.append_assoc, List.singleton_append]
  · intro j hjO hjW hj1 hj2
    rw [hs6oth j hj2, hs5oth j hjW hj2, hs4oth j hj1 hj2, hs3oth j hjO, hs2oth j hjO hj1,
      hs1othX j hj2]

end Work.IntLib
