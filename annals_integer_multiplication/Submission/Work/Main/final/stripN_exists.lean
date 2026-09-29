import Mathlib
import Submission.Work.Main.defs

namespace Work.Main.final

/-- Every primitive step of StackLang costs at least one unit. -/
theorem eval_cost_pos {main c : HvdH.Cmd} {s s' : HvdH.State} {n : ℕ}
    (h : HvdH.Eval main c s s' n) : 1 ≤ n := by
  induction h <;> omega

/-- `stripAux stripProg n` runs `stripProg` `n` times in sequence. -/
def stripAux (stripProg : HvdH.Cmd) : ℕ → HvdH.Cmd
  | 0 => HvdH.Cmd.skip
  | (n + 1) => HvdH.Cmd.seq stripProg (stripAux stripProg n)

/-- The cost recurrence of stripping: one single-value strip at rate `C0*(A+V+1)` followed by a
bulk strip of total size `T` at the leaner rate `(n+1)*C0*(A+T+1)` still fits in
`(n+2)*C0*(A+(V+T)+1)`. -/
theorem strip_cost_le (n C0 A V T : ℕ) :
    C0 * (A + V + 1) + (n + 1) * C0 * (A + T + 1) ≤ (n + 2) * C0 * (A + (V + T) + 1) := by
  have h1 : C0 * (A + V + 1) + (n + 1) * C0 * (A + T + 1)
      = C0 * ((A + V + 1) + (n + 1) * (A + T + 1)) := by ring
  have h2 : C0 * ((n + 2) * (A + (V + T) + 1)) = (n + 2) * C0 * (A + (V + T) + 1) := by ring
  have h3 : (n + 2) * (A + (V + T) + 1)
      = ((A + V + 1) + (n + 1) * (A + T + 1)) + ((n + 1) * V + T) := by ring
  rw [h1, ← h2, h3]
  exact Nat.mul_le_mul le_rfl (Nat.le_add_right _ _)

theorem stripN_exists (hKer : HvdH.KernelLib) (stripProg : HvdH.Cmd) (C0 : ℕ)
    (hP : ∀ (main : HvdH.Cmd) (a b v : HvdH.Val) (rest : List HvdH.Val),
      HvdH.WordR main stripProg (fun vs => vs = a :: b :: v :: rest) (fun _ out => out = a :: b :: rest)
        (fun _ => C0 * (HvdH.vsz a + HvdH.vsz b + HvdH.vsz v + 1))) :
    ∃ (stripN : ℕ → HvdH.Cmd), ∀ (n : ℕ) (main : HvdH.Cmd) (a b : HvdH.Val) (us R : List HvdH.Val),
      us.length = n →
      HvdH.WordR main (stripN n) (fun vs => vs = a :: b :: us ++ R) (fun _ out => out = a :: b :: R)
        (fun _ => (n + 1) * C0 * (HvdH.vsz a + HvdH.vsz b + (us.map HvdH.vsz).sum + 1)) := by
  -- `hP` supplies a `WordR` cost bound; since every `Eval` run costs at least a step, `C0 ≥ 1`.
  have hC0 : 1 ≤ C0 := by
    obtain ⟨out, s', n, -, hev, hcost, -, -⟩ :=
      hP HvdH.Cmd.skip HvdH.Val.nil HvdH.Val.nil HvdH.Val.nil []
        [HvdH.Val.nil, HvdH.Val.nil, HvdH.Val.nil] rfl
        ⟨fun _ => HvdH.Glyph.eos,
          fun k => if k = 0 then HvdH.encs [HvdH.Val.nil, HvdH.Val.nil, HvdH.Val.nil] else []⟩
        ([] : List HvdH.Glyph) (by simp)
    have h1 : 1 ≤ n := eval_cost_pos hev
    have h2 : n ≤ C0 *
        (HvdH.vsz HvdH.Val.nil + HvdH.vsz HvdH.Val.nil + HvdH.vsz HvdH.Val.nil + 1) := hcost
    by_contra hlt
    have h0 : C0 = 0 := by omega
    rw [h0, Nat.zero_mul] at h2
    omega
  refine ⟨stripAux stripProg, ?_⟩
  intro n
  induction n with
  | zero =>
      intro main a b us R hus
      cases us with
      | nil =>
        refine hKer.conseq main HvdH.Cmd.skip (fun _ => True) (fun vs => vs = a :: b :: R)
          (fun vs out => out = vs) (fun _ out => out = a :: b :: R) (fun _ => 1)
          (fun _ => (0 + 1) * C0 *
            (HvdH.vsz a + HvdH.vsz b + (([].map HvdH.vsz).sum) + 1))
          (hKer.skip main) (fun vs _ => trivial) ?_ ?_
        · intro vs out hv hout
          rw [hout]; exact hv
        · intro vs _
          have hfac : 1 ≤ HvdH.vsz a + HvdH.vsz b + 1 := by omega
          have hle : 1 ≤ C0 * (HvdH.vsz a + HvdH.vsz b + 1) := by
            simpa using Nat.mul_le_mul hC0 hfac
          calc (1 : ℕ) ≤ C0 * (HvdH.vsz a + HvdH.vsz b + 1) := hle
            _ = (0 + 1) * C0 *
                  (HvdH.vsz a + HvdH.vsz b + (([].map HvdH.vsz).sum) + 1) := by
                  simp only [List.map_nil, List.sum_nil, Nat.add_zero]
                  ring
      | cons v us' => simp at hus
  | succ n ih =>
      intro main a b us R hus
      cases us with
      | nil => simp at hus
      | cons v us' =>
        have hus' : us'.length = n := by simpa using hus
        have hseq := hKer.seq main stripProg (stripAux stripProg n)
          (fun vs => vs = a :: b :: (v :: us') ++ R)
          (fun _ out => out = a :: b :: us' ++ R)
          (fun _ => C0 * (HvdH.vsz a + HvdH.vsz b + HvdH.vsz v + 1))
          (fun vs => vs = a :: b :: us' ++ R)
          (fun _ out => out = a :: b :: R)
          (fun _ => (n + 1) * C0 * (HvdH.vsz a + HvdH.vsz b + (us'.map HvdH.vsz).sum + 1))
          (fun _ => (n + 1) * C0 * (HvdH.vsz a + HvdH.vsz b + (us'.map HvdH.vsz).sum + 1))
          (hP main a b v (us' ++ R))
          (ih main a b us' R hus')
          (fun vs mid _ hmid => ⟨hmid, le_refl _⟩)
        refine hKer.conseq main (HvdH.Cmd.seq stripProg (stripAux stripProg n))
          (fun vs => vs = a :: b :: (v :: us') ++ R)
          (fun vs => vs = a :: b :: (v :: us') ++ R)
          (fun vs out => ∃ mid, mid = a :: b :: us' ++ R ∧ out = a :: b :: R)
          (fun _ out => out = a :: b :: R)
          (fun _ => C0 * (HvdH.vsz a + HvdH.vsz b + HvdH.vsz v + 1)
            + (n + 1) * C0 * (HvdH.vsz a + HvdH.vsz b + (us'.map HvdH.vsz).sum + 1))
          (fun _ => (n + 1 + 1) * C0 *
            (HvdH.vsz a + HvdH.vsz b + ((v :: us').map HvdH.vsz).sum + 1))
          hseq (fun vs h => h) (fun vs out _ h => h.elim (fun mid hm => hm.2)) ?_
        · intro vs _
          show C0 * (HvdH.vsz a + HvdH.vsz b + HvdH.vsz v + 1)
              + (n + 1) * C0 * (HvdH.vsz a + HvdH.vsz b + (us'.map HvdH.vsz).sum + 1)
            ≤ (n + 1 + 1) * C0 *
              (HvdH.vsz a + HvdH.vsz b + ((v :: us').map HvdH.vsz).sum + 1)
          rw [List.map_cons, List.sum_cons]
          exact strip_cost_le n C0 (HvdH.vsz a + HvdH.vsz b) (HvdH.vsz v) (us'.map HvdH.vsz).sum

end Work.Main.final
