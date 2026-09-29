import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.Kernel.Raw
import Submission.Work.Transform.arrangeDefs

namespace Work.Transform

open HvdH

set_option autoImplicit false

/-- A pure data-shuffling word (no arithmetic): rearrange the working stack
`[a, ab, zst, zstie, p, r, ts', zs]` into the layout the Transform pipeline consumes, duplicating
`p`, `r`, `ab`, `zst` as needed (the input `a`, `ab`, `zst`, `zstie` are lists of fixed-point
pairs, `ts'` is a list of naturals, `zs` the input vector).  `Kernel.roll`/`pick`/`dup`/`drop`
suffice; the cost is linear in the total encoding size of *all* the values manipulated, including
`int p`, `int r` and `intList ts'` (the output contains 5 copies of `int p`, 4 of `int r`, 2 of
`intList ts'`). -/
theorem arrangeWord : HvdH.KernelLib → ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p r : ℕ) (ts' : List ℕ) (zs zst zstie a ab : List (ℤ × ℤ))
      (R : List HvdH.Val),
      HvdH.WordR main prog
        (fun vs => vs = HvdH.cvecVal a :: HvdH.cvecVal ab :: HvdH.cvecVal zst ::
          HvdH.cvecVal zstie :: HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' ::
          HvdH.cvecVal zs :: R)
        (fun vs out => out = HvdH.Val.int p :: HvdH.cvecVal ab :: HvdH.cvecVal zs ::
          HvdH.cvecVal zst :: HvdH.Val.int r :: HvdH.Val.int p :: HvdH.cvecVal a ::
          HvdH.cvecVal zst :: HvdH.Val.int r :: HvdH.Val.int p :: HvdH.Val.int p ::
          HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: HvdH.Val.int p ::
          HvdH.Val.int r :: HvdH.intList ts' :: R)
        (fun _ => K * ((((HvdH.vsz (HvdH.cvecVal zst) + HvdH.vsz (HvdH.cvecVal zstie)) +
          HvdH.vsz (HvdH.cvecVal a)) + HvdH.vsz (HvdH.cvecVal ab) +
          HvdH.vsz (HvdH.cvecVal zs) + HvdH.vsz (HvdH.Val.int p) + HvdH.vsz (HvdH.Val.int r) +
          HvdH.vsz (HvdH.intList ts')) * 3000 + 1) + K) := by
  intro hl
  obtain ⟨pickP, Kp, hpk⟩ := hl.pick
  obtain ⟨rollP, Kr, hrl⟩ := hl.roll
  refine ⟨progOf (fun s => if s.1 then pickP s.2 else rollP s.2) plan, 2000 * max Kp Kr + 1000, ?_⟩
  intro main p r ts' zs zst zstie a ab R
  -- the eight working values, in pool order
  set pool : List Val := [cvecVal a, cvecVal ab, cvecVal zst, cvecVal zstie, Val.int p,
    Val.int r, intList ts', cvecVal zs] with hpoolDef
  have hpool : pool.length = 8 := by rw [hpoolDef]; rfl
  have hS : ∀ v ∈ pool, vsz v ≤ (pool.map vsz).sum :=
    fun v hv => List.le_sum_of_mem (List.mem_map_of_mem hv)
  -- one step of the plan
  have hstep : ∀ (m : Bool) (k : ℕ) (l : List I8), k < l.length →
      WordR main (if m then pickP k else rollP k) (fun vs => vs = stateOf pool l ++ R)
        (fun _ out => out = stateOf pool (stepL l (m, k)) ++ R)
        (fun _ => stepCost (max Kp Kr) (pool.map vsz).sum (m, k)) := by
    intro m k l hk
    cases m with
    | false =>
      simpa using rollStep (hK := le_max_right Kp Kr) (hrl main k) hpool hS R l hk
    | true =>
      simpa using pickStep (hK := le_max_left Kp Kr) (hpk main k) hpool hS R l hk
  have hrun := runPlan (pool := pool) (fun s => if s.1 then pickP s.2 else rollP s.2) R
    (max Kp Kr) (pool.map vsz).sum hstep plan L0 plan_indices
  -- the concrete pool states
  have hL0 : stateOf pool L0 = [cvecVal a, cvecVal ab, cvecVal zst, cvecVal zstie, Val.int p,
      Val.int r, intList ts', cvecVal zs] := by
    rw [hpoolDef]; rfl
  have hLfin : stateOf pool planFinal = [Val.int p, cvecVal ab, cvecVal zs, cvecVal zst,
      Val.int r, Val.int p, cvecVal a, cvecVal zst, Val.int r, Val.int p, Val.int p,
      cvecVal zstie, Val.int r, cvecVal ab, Val.int p, Val.int r, intList ts'] := by
    rw [hpoolDef]; rfl
  have hsum : (pool.map vsz).sum = ((((vsz (cvecVal zst) + vsz (cvecVal zstie)) + vsz (cvecVal a))
      + vsz (cvecVal ab) + vsz (cvecVal zs) + vsz (Val.int p) + vsz (Val.int r)
      + vsz (intList ts'))) := by
    rw [hpoolDef]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  refine Work.Kernel.WordR_conseq hrun ?_ ?_ ?_
  · intro vs hvs
    rw [hvs, hL0]
    rfl
  · intro vs out hvs hout
    rw [hout, plan_foldl, hLfin]
    rfl
  · intro vs _
    have h1 := planCost_le (Kmax := max Kp Kr) (S := (pool.map vsz).sum) (Bnd := 17) plan
      plan_mem_lt
    rw [plan_length] at h1
    have h2 : 17 * (max Kp Kr * 17 * (17 * (pool.map vsz).sum + 1)) + 1 ≤
        (2000 * max Kp Kr + 1000) *
          ((((vsz (cvecVal zst) + vsz (cvecVal zstie)) + vsz (cvecVal a)) + vsz (cvecVal ab)
            + vsz (cvecVal zs) + vsz (Val.int p) + vsz (Val.int r) + vsz (intList ts'))
            * 3000 + 1) + (2000 * max Kp Kr + 1000) := by
      rw [hsum]
      nlinarith [Nat.zero_le (max Kp Kr), Nat.zero_le (pool.map vsz).sum]
    exact le_trans h1 h2

end Work.Transform
