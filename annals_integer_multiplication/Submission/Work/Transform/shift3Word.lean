import Mathlib
import Submission.Work.Transform.Defs

namespace Work.Transform

open HvdH

/-- One `KernelLib.roll k` step, transported to a state that is *exactly* a list `L` of values:
`roll k` costs `K0 * (k+1) * (Σ_{i ≤ k} vsz Lᵢ + 1)` and is available whenever `k < L.length`. -/
private theorem shift3_rollAt (hK : KernelLib) {main : Cmd} {prog : ℕ → Cmd} {K0 : ℕ}
    (h : ∀ k : ℕ, WordR main (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K0 * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : ℕ) (L : List Val) (hk : k < L.length) (c : ℕ)
    (hc : K0 * (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ c) :
    WordR main (prog k) (fun vs => vs = L)
      (fun _ out => out = L.getD k .nil :: L.eraseIdx k) (fun _ => c) := by
  refine hK.conseq main (prog k) (fun vs => k < vs.length) (fun vs => vs = L)
    (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
    (fun _ out => out = L.getD k .nil :: L.eraseIdx k)
    (fun vs => K0 * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)) (fun _ => c)
    (h k) ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; exact hk
  · intro vs out hvs hq; rw [hvs] at hq; exact hq
  · intro vs hvs; rw [hvs]; exact hc

/-- Sequential composition of two words with *exact* pre/post states (costs add). -/
private theorem shift3_seqExact (hK : KernelLib) {main p q : Cmd} {L M N : List Val} {c c' : ℕ}
    (hp : WordR main p (fun vs => vs = L) (fun _ out => out = M) (fun _ => c))
    (hq : WordR main q (fun vs => vs = M) (fun _ out => out = N) (fun _ => c')) :
    WordR main (Cmd.seq p q) (fun vs => vs = L) (fun _ out => out = N) (fun _ => c + c') := by
  have h := hK.seq main p q (fun vs => vs = L) (fun _ out => out = M) (fun _ => c)
    (fun vs => vs = M) (fun _ out => out = N) (fun _ => c') (fun _ => c') hp hq
    (fun vs mid _ hM => ⟨hM, le_refl _⟩)
  refine hK.conseq main (Cmd.seq p q) (fun vs => vs = L) (fun vs => vs = L)
    (fun vs out => ∃ mid, mid = M ∧ out = N) (fun _ out => out = N)
    (fun _ => c + c') (fun _ => c + c') h (fun _ hh => hh) ?_ (fun _ _ => le_refl _)
  intro vs out _ hpost
  obtain ⟨mid, -, hout⟩ := hpost
  exact hout

/-- A small stack-shuffle word: transform `x :: y :: z :: w :: v :: Rest` into
`x :: y :: w :: v :: z :: Rest` (i.e. move the third value past the next two).  The first two
values and everything below are restored; the cost is linear in the sizes of the five values.
Realised by composing `Kernel.roll`: `roll 4; roll 4; roll 3; roll 3` maps
`[x,y,z,w,v] → [v,x,y,z,w] → [w,v,x,y,z] → [y,w,v,x,z] → [x,y,w,v,z]`. -/
theorem shift3Word : HvdH.KernelLib → ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (x y z w v : HvdH.Val) (Rest : List HvdH.Val),
      HvdH.WordR main prog
        (fun vs => vs = x :: y :: z :: w :: v :: Rest)
        (fun vs out => out = x :: y :: w :: v :: z :: Rest)
        (fun _ => K * (HvdH.vsz x + HvdH.vsz y + HvdH.vsz z + HvdH.vsz w + HvdH.vsz v + 1) + K) := by
  intro hK
  obtain ⟨rollP, Kr, hrl⟩ := hK.roll
  -- `roll 4; roll 4; roll 3; roll 3`
  refine ⟨Cmd.seq (Cmd.seq (rollP 4) (rollP 4)) (Cmd.seq (rollP 3) (rollP 3)), 18 * Kr, ?_⟩
  intro main x y z w v Rest
  -- one step: every `roll` costs `Kr * (k+1) * (prefix sum + 1)`, and every prefix sum here is
  -- bounded by `Σ vsz` of the five values.
  have hc1 : Kr * 5 * ((((x :: y :: z :: w :: v :: Rest).take 5).map vsz).sum + 1)
      ≤ Kr * 5 * (vsz x + vsz y + vsz z + vsz w + vsz v + 1) := by
    have hs : ((((x :: y :: z :: w :: v :: Rest).take 5).map vsz).sum)
        ≤ vsz x + vsz y + vsz z + vsz w + vsz v := by simp; omega
    exact Nat.mul_le_mul_left (Kr * 5) (Nat.succ_le_succ hs)
  have h1 : WordR main (rollP 4) (fun vs => vs = x :: y :: z :: w :: v :: Rest)
      (fun _ out => out = v :: x :: y :: z :: w :: Rest)
      (fun _ => Kr * 5 * (vsz x + vsz y + vsz z + vsz w + vsz v + 1)) := by
    simpa using shift3_rollAt hK (hrl main) 4 (x :: y :: z :: w :: v :: Rest) (by simp)
      (Kr * 5 * (vsz x + vsz y + vsz z + vsz w + vsz v + 1)) hc1
  have hc2 : Kr * 5 * ((((v :: x :: y :: z :: w :: Rest).take 5).map vsz).sum + 1)
      ≤ Kr * 5 * (vsz x + vsz y + vsz z + vsz w + vsz v + 1) := by
    have hs : ((((v :: x :: y :: z :: w :: Rest).take 5).map vsz).sum)
        ≤ vsz x + vsz y + vsz z + vsz w + vsz v := by simp; omega
    exact Nat.mul_le_mul_left (Kr * 5) (Nat.succ_le_succ hs)
  have h2 : WordR main (rollP 4) (fun vs => vs = v :: x :: y :: z :: w :: Rest)
      (fun _ out => out = w :: v :: x :: y :: z :: Rest)
      (fun _ => Kr * 5 * (vsz x + vsz y + vsz z + vsz w + vsz v + 1)) := by
    simpa using shift3_rollAt hK (hrl main) 4 (v :: x :: y :: z :: w :: Rest) (by simp)
      (Kr * 5 * (vsz x + vsz y + vsz z + vsz w + vsz v + 1)) hc2
  have hc3 : Kr * 4 * ((((w :: v :: x :: y :: z :: Rest).take 4).map vsz).sum + 1)
      ≤ Kr * 4 * (vsz x + vsz y + vsz z + vsz w + vsz v + 1) := by
    have hs : ((((w :: v :: x :: y :: z :: Rest).take 4).map vsz).sum)
        ≤ vsz x + vsz y + vsz z + vsz w + vsz v := by simp; omega
    exact Nat.mul_le_mul_left (Kr * 4) (Nat.succ_le_succ hs)
  have h3 : WordR main (rollP 3) (fun vs => vs = w :: v :: x :: y :: z :: Rest)
      (fun _ out => out = y :: w :: v :: x :: z :: Rest)
      (fun _ => Kr * 4 * (vsz x + vsz y + vsz z + vsz w + vsz v + 1)) := by
    simpa using shift3_rollAt hK (hrl main) 3 (w :: v :: x :: y :: z :: Rest) (by simp)
      (Kr * 4 * (vsz x + vsz y + vsz z + vsz w + vsz v + 1)) hc3
  have hc4 : Kr * 4 * ((((y :: w :: v :: x :: z :: Rest).take 4).map vsz).sum + 1)
      ≤ Kr * 4 * (vsz x + vsz y + vsz z + vsz w + vsz v + 1) := by
    have hs : ((((y :: w :: v :: x :: z :: Rest).take 4).map vsz).sum)
        ≤ vsz x + vsz y + vsz z + vsz w + vsz v := by simp; omega
    exact Nat.mul_le_mul_left (Kr * 4) (Nat.succ_le_succ hs)
  have h4 : WordR main (rollP 3) (fun vs => vs = y :: w :: v :: x :: z :: Rest)
      (fun _ out => out = x :: y :: w :: v :: z :: Rest)
      (fun _ => Kr * 4 * (vsz x + vsz y + vsz z + vsz w + vsz v + 1)) := by
    simpa using shift3_rollAt hK (hrl main) 3 (y :: w :: v :: x :: z :: Rest) (by simp)
      (Kr * 4 * (vsz x + vsz y + vsz z + vsz w + vsz v + 1)) hc4
  have h12 := shift3_seqExact hK h1 h2
  have h34 := shift3_seqExact hK h3 h4
  have hall := shift3_seqExact hK h12 h34
  -- total cost `5 + 5 + 4 + 4 = 18` linear units
  refine hK.conseq main _ (fun vs => vs = x :: y :: z :: w :: v :: Rest)
    (fun vs => vs = x :: y :: z :: w :: v :: Rest) (fun _ out => out = x :: y :: w :: v :: z :: Rest)
    (fun _ out => out = x :: y :: w :: v :: z :: Rest) _ _ hall (fun _ h => h) (fun _ _ _ h => h) ?_
  intro vs _
  have heq : Kr * 5 * (vsz x + vsz y + vsz z + vsz w + vsz v + 1) +
        Kr * 5 * (vsz x + vsz y + vsz z + vsz w + vsz v + 1) +
        (Kr * 4 * (vsz x + vsz y + vsz z + vsz w + vsz v + 1) +
         Kr * 4 * (vsz x + vsz y + vsz z + vsz w + vsz v + 1))
      = 18 * Kr * (vsz x + vsz y + vsz z + vsz w + vsz v + 1) := by ring
  rw [heq]
  exact Nat.le_add_right _ _

end Work.Transform
