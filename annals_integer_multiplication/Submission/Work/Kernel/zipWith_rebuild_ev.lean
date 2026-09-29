import Mathlib
import Submission.Work.Kernel.zipWithDefs
import Submission.Work.Kernel.zipWith_rebuildBody_miss
import Submission.Work.Kernel.zipWith_rebuildBody_hit

/-!
# Kernel: the *rebuild* loop of `zipWith`

`Work.Kernel.zipWith_rebuildProg` is the last loop of `zipWith`: starting from

* stack `3` = `encs w ++ gMark :: B3` (the results of the main loop, in reverse order, above the
  frame marker `gMark`), and
* stack `0` = `encs (ofList acc :: rest0) ++ R` (the value stack),

it peels the values of `w` off stack `3` one at a time (top first, i.e. the *last* result first),
moves each of them to the value stack and pushes a `cons` glyph on top of it, and stops when the
marker `gMark` becomes visible.  This rebuilds `ofList (w.reverse ++ acc)` above `rest0` and pops
the marker, restoring stack `3` to `B3`.

Cost of one iteration with `vsz v ≤ L`: `1` (`peek`) `+ 1` (`ite` test) `+ 16 * (vsz v + 1)`
(`mvVal`) `+ 2` (`pushConst`) `+ 1` (`set`) plus the loop test `1`, i.e. `≤ 16 * (L + 1) + 6`.  The
last iteration (marker on top of stack 3) costs `4 + 1`, and the terminating test `1` more, giving
`w.length * (16 * (L + 1) + 6) + 6` in total.
-/

set_option autoImplicit false

namespace Work.Kernel

open HvdH
open Work.Layout

/-- The head of `v.enc ++ A` is never the frame marker `gMark` (`gMark` = `Glyph.mk 7` does not
occur in any `Val.enc`): this is what makes the `ite` of `zipWith_rebuildBody` take the *moving*
branch when stack 3 carries a value. -/
theorem zipWith_rebuild_headD_ne_gMark (v : HvdH.Val) (A : List HvdH.Glyph) :
    (v.enc ++ A).headD HvdH.Glyph.eos ≠ Work.Layout.gMark := by
  intro h
  cases v with
  | int z =>
    by_cases hz : z < 0
    · exact Work.Layout.gMark_ne_neg (by simpa [HvdH.Val.enc, hz] using h.symm)
    · exact Work.Layout.gMark_ne_pos (by simpa [HvdH.Val.enc, hz] using h.symm)
  | nil => exact Work.Layout.gMark_ne_nil (by simpa [HvdH.Val.enc] using h.symm)
  | cons a b => exact Work.Layout.gMark_ne_cons (by simpa [HvdH.Val.enc] using h.symm)

/-- The rebuild loop, by induction on `w` (which is processed from the top of stack 3 downwards,
so the result is `w.reverse ++ acc`).  The loop runs `w.length + 1` times (the extra iteration sees
the marker and stops).  Cost `≤ w.length * (16 * (L + 1) + 6) + 5`, which is the loop bound
*including* the per-iteration tests but *without* the terminating test. -/
theorem zipWith_rebuild_loop (main : HvdH.Cmd) (L : ℕ) :
    ∀ (ws acc rest0 : List HvdH.Val) (R B3 : List HvdH.Glyph) (s : HvdH.State),
      (∀ v ∈ ws, vsz v ≤ L) →
      s.reg rLoopG = Glyph.cons →
      s.stk 3 = encs ws ++ gMark :: B3 →
      s.stk 0 = encs (ofList acc :: rest0) ++ R →
      ∃ s' C, loopRuns main rLoopG Glyph.cons zipWith_rebuildBody (ws.length + 1) s s' C ∧
        C ≤ ws.length * (16 * (L + 1) + 6) + 5 ∧
        s'.stk 0 = encs (ofList (ws.reverse ++ acc) :: rest0) ++ R ∧
        s'.stk 3 = B3 ∧ s'.reg rLoopG = Glyph.eos ∧
        (∀ j, j ≠ 0 → j ≠ 3 → s'.stk j = s.stk j) := by
  intro ws
  induction ws with
  | nil =>
    -- the marker is already on top: one iteration (cost `4`) then the loop test fails (cost `1`)
    intro acc rest0 R B3 s hsz hreg h3 h0
    obtain ⟨s', n, hev, hn, h3', h0', hr', hfr'⟩ := zipWith_rebuildBody_hit main h3 hreg
    refine ⟨s', 5, loopRuns.one hreg ⟨n, hev, hn⟩, ?_, ?_, h3', hr', hfr'⟩
    · omega
    · rw [h0', h0]; simp
  | cons v ws' ih =>
    -- move the value `v` sitting on top of stack 3 down to the value stack, push `cons`, recurse
    intro acc rest0 R B3 s hsz hreg h3 h0
    have hv : vsz v ≤ L := hsz v (List.mem_cons_self ..)
    have hsz' : ∀ x ∈ ws', vsz x ≤ L := fun x hx => hsz x (List.mem_cons_of_mem v hx)
    have h3' : s.stk 3 = v.enc ++ (encs ws' ++ gMark :: B3) := by
      rw [h3, encs_cons, List.append_assoc]
    obtain ⟨s₁, n₁, hev₁, hn₁, h3₁, h0₁, hr₁, hfr₁⟩ :=
      zipWith_rebuildBody_miss main (A := encs ws' ++ gMark :: B3) h3'
        (zipWith_rebuild_headD_ne_gMark v (encs ws' ++ gMark :: B3))
    have hn₁' : n₁ ≤ 16 * (L + 1) + 5 := by omega
    have h0₁' : s₁.stk 0 = encs (ofList (v :: acc) :: rest0) ++ R := by
      rw [h0₁, h0, zipWith_encs_ofList_cons]
      simp only [List.cons_append, List.append_assoc]
    obtain ⟨s₂, C₂, hrun₂, hC₂, h0₂, h3₂, hr₂, hfr₂⟩ :=
      ih (v :: acc) rest0 R B3 s₁ hsz' hr₁ h3₁ h0₁'
    have hrev : (v :: ws').reverse ++ acc = ws'.reverse ++ (v :: acc) := by
      rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    have h0₂' : s₂.stk 0 = encs (ofList ((v :: ws').reverse ++ acc) :: rest0) ++ R := by
      rw [hrev, h0₂]
    refine ⟨s₂, 16 * (L + 1) + 5 + C₂ + 1,
      loopRuns.succ' hreg ⟨n₁, hev₁, hn₁'⟩ hrun₂ (le_refl _), ?_, h0₂', h3₂, hr₂, ?_⟩
    · have hkey : (v :: ws').length * (16 * (L + 1) + 6) + 5
          = ws'.length * (16 * (L + 1) + 6) + 5 + (16 * (L + 1) + 6) := by
        simp only [List.length_cons]; ring
      rw [hkey]; omega
    · intro j hj0 hj3; rw [hfr₂ j hj0 hj3, hfr₁ j hj0 hj3]

/-- **Rebuild loop of `zipWith`.**  If stack 3 carries the reversed results `encs w` above the
marker `gMark` and the value stack carries `ofList acc :: rest0`, then `zipWith_rebuildProg` rebuilds
`ofList (w.reverse ++ acc) :: rest0` on the value stack, pops the marker (so that stack 3 becomes
`B3`), restores every other stack, and costs at most `w.length * (16 * (L + 1) + 6) + 6` steps when
every value of `w` has size `≤ L`. -/
theorem zipWith_rebuild_ev (main : HvdH.Cmd) (L : ℕ) :
    ∀ (w acc : List HvdH.Val) (s : HvdH.State) (B3 R : List HvdH.Glyph) (rest0 : List HvdH.Val),
      (∀ v ∈ w, HvdH.vsz v ≤ L) →
      s.stk 3 = HvdH.encs w ++ Work.Layout.gMark :: B3 →
      s.stk 0 = HvdH.encs (HvdH.ofList acc :: rest0) ++ R →
      s.reg Work.Layout.rLoopG = HvdH.Glyph.cons →
      ∃ s' n, HvdH.Eval main Work.Kernel.zipWith_rebuildProg s s' n ∧
        n ≤ w.length * (16 * (L + 1) + 6) + 6 ∧
        s'.stk 0 = HvdH.encs (HvdH.ofList (w.reverse ++ acc) :: rest0) ++ R ∧ s'.stk 3 = B3 ∧
        (∀ j, j ≠ 0 → j ≠ 3 → s'.stk j = s.stk j) := by
  intro w acc s B3 R rest0 hsz h3 h0 hreg
  obtain ⟨s', C, hrun, hC, h0', h3', hr', hfr'⟩ :=
    zipWith_rebuild_loop main L w acc rest0 R B3 s hsz hreg h3 h0
  -- the loop stops because the flag was set to `eos` on the marker iteration
  have hne : s'.reg rLoopG ≠ Glyph.cons := by rw [hr']; decide
  obtain ⟨n, hev, hn⟩ := loopRuns.eval' hrun hne
  refine ⟨s', n, ?_, ?_, h0', h3', hfr'⟩
  · simpa [zipWith_rebuildProg] using hev
  · omega

end Work.Kernel
