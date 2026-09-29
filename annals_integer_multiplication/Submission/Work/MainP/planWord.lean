import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Transform.arrangeDefs

/-!
# `Work.MainP.planWord`: a generic data-shuffling word

Generic form of `Work.Transform.arrangeWord`.  Given a pool of exactly eight values and a plan of
`pick`/`roll` steps (indices into the *pool*, not into the stack), `planWord` computes the word
that transforms the value stack `stateOf pool L0 ++ tail` into
`stateOf pool (plan.foldl stepL L0) ++ tail`, with a cost linear in the total encoding size of the
pool.  The plan is data: the caller fixes it as a literal, so the resulting `Cmd` is a fixed
program.  `planWordL` is the same with a uniform size bound for the pool.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.MainP

open HvdH

/-- A generic data-shuffling word (see the module docstring). -/
theorem planWord (hK : HvdH.KernelLib) :
    ∃ (prog : List (Bool × ℕ) → HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (pool : List HvdH.Val) (L0 : List Work.Transform.I8)
        (plan : List (Bool × ℕ)) (Bnd : ℕ) (tail : List HvdH.Val),
        pool.length = 8 →
        (∀ s ∈ plan, s.2 < Bnd) →
        (∀ j, j < plan.length → (plan.getD j (true, 0)).2
            < ((plan.take j).foldl Work.Transform.stepL L0).length) →
        HvdH.WordR main (prog plan)
          (fun vs => vs = Work.Transform.stateOf pool L0 ++ tail)
          (fun _ out => out = Work.Transform.stateOf pool
            (plan.foldl Work.Transform.stepL L0) ++ tail)
          (fun _ => K * (Bnd * ((Bnd * (pool.map HvdH.vsz).sum + 1) * (plan.length + 1))) + K) := by
  obtain ⟨pickP, Kp, hpk⟩ := hK.pick
  obtain ⟨rollP, Kr, hrl⟩ := hK.roll
  refine ⟨fun plan => Work.Transform.progOf (fun s => if s.1 then pickP s.2 else rollP s.2) plan,
    max (max Kp Kr) 1 + 1, ?_⟩
  intro main pool L0 plan Bnd tail hpool hBnd hrange
  have hS : ∀ v ∈ pool, HvdH.vsz v ≤ (pool.map HvdH.vsz).sum :=
    fun v hv => List.le_sum_of_mem (List.mem_map_of_mem hv)
  have hstep : ∀ (m : Bool) (k : ℕ) (l : List Work.Transform.I8), k < l.length →
      HvdH.WordR main (if m then pickP k else rollP k)
        (fun vs => vs = Work.Transform.stateOf pool l ++ tail)
        (fun _ out => out = Work.Transform.stateOf pool (Work.Transform.stepL l (m, k)) ++ tail)
        (fun _ => Work.Transform.stepCost (max Kp Kr) (pool.map HvdH.vsz).sum (m, k)) := by
    intro m k l hk
    cases m with
    | false =>
      simpa using Work.Transform.rollStep (hK := le_max_right Kp Kr)
        (hrl main k) hpool hS tail l hk
    | true =>
      simpa using Work.Transform.pickStep (hK := le_max_left Kp Kr)
        (hpk main k) hpool hS tail l hk
  have hrun := Work.Transform.runPlan (fun s => if s.1 then pickP s.2 else rollP s.2) tail
    (max Kp Kr) (pool.map HvdH.vsz).sum hstep plan L0 hrange
  refine Work.Kernel.WordR_conseq hrun (fun _ h => h) (fun _ _ _ h => h) ?_
  intro vs _
  have h1 := Work.Transform.planCost_le (Kmax := max Kp Kr) (S := (pool.map HvdH.vsz).sum)
    (Bnd := Bnd) plan hBnd
  set M : ℕ := max (max Kp Kr) 1 + 1 with hM
  have hKle : max Kp Kr ≤ M := by omega
  have hMpos : 1 ≤ M := by omega
  have hlen : plan.length ≤ plan.length + 1 := Nat.le_succ _
  calc Work.Transform.planCost (max Kp Kr) (pool.map HvdH.vsz).sum plan
      ≤ plan.length * ((max Kp Kr) * Bnd * (Bnd * (pool.map HvdH.vsz).sum + 1)) + 1 := h1
    _ ≤ M * (plan.length * (Bnd * (Bnd * (pool.map HvdH.vsz).sum + 1))) + M := by
        refine Nat.add_le_add ?_ hMpos
        calc plan.length * ((max Kp Kr) * Bnd * (Bnd * (pool.map HvdH.vsz).sum + 1))
            = (max Kp Kr) * (plan.length * (Bnd * (Bnd * (pool.map HvdH.vsz).sum + 1))) := by
              ring
          _ ≤ M * (plan.length * (Bnd * (Bnd * (pool.map HvdH.vsz).sum + 1))) :=
              Nat.mul_le_mul_right _ hKle
    _ ≤ M * (Bnd * ((Bnd * (pool.map HvdH.vsz).sum + 1) * (plan.length + 1))) + M := by
        have h4 : plan.length * (Bnd * (Bnd * (pool.map HvdH.vsz).sum + 1))
            ≤ Bnd * ((Bnd * (pool.map HvdH.vsz).sum + 1) * (plan.length + 1)) := by
          calc plan.length * (Bnd * (Bnd * (pool.map HvdH.vsz).sum + 1))
              = Bnd * ((Bnd * (pool.map HvdH.vsz).sum + 1) * plan.length) := by ring
            _ ≤ Bnd * ((Bnd * (pool.map HvdH.vsz).sum + 1) * (plan.length + 1)) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlen)
        exact Nat.add_le_add (Nat.mul_le_mul_left M h4) le_rfl

/-- `planWord` with a uniform size bound `L` for the eight pool values. -/
theorem planWordL (hK : HvdH.KernelLib) :
    ∃ (prog : List (Bool × ℕ) → HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (pool : List HvdH.Val) (L0 : List Work.Transform.I8)
        (plan : List (Bool × ℕ)) (Bnd L : ℕ) (tail : List HvdH.Val),
        pool.length = 8 → (∀ v ∈ pool, HvdH.vsz v ≤ L) →
        (∀ s ∈ plan, s.2 < Bnd) →
        (∀ j, j < plan.length → (plan.getD j (true, 0)).2
            < ((plan.take j).foldl Work.Transform.stepL L0).length) →
        HvdH.WordR main (prog plan)
          (fun vs => vs = Work.Transform.stateOf pool L0 ++ tail)
          (fun _ out => out = Work.Transform.stateOf pool
            (plan.foldl Work.Transform.stepL L0) ++ tail)
          (fun _ => K * (Bnd * ((Bnd * (L + 1) * 8 + 1) * (plan.length + 1))) + K) := by
  obtain ⟨prog, K0, h0⟩ := planWord hK
  refine ⟨prog, 2 * K0 + 1, ?_⟩
  intro main pool L0 plan Bnd L tail hlen hL hBnd hrange
  have hX := h0 main pool L0 plan Bnd tail hlen hBnd hrange
  refine Work.Kernel.WordR_conseq hX (fun _ h => h) (fun _ _ _ h => h) ?_
  intro vs _
  have hsum : ∀ (l : List HvdH.Val), (∀ v ∈ l, HvdH.vsz v ≤ L) → (l.map HvdH.vsz).sum ≤ l.length * L := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a t ih =>
      intro h
      have ha : HvdH.vsz a ≤ L := h a (by simp)
      have ht : ∀ v ∈ t, HvdH.vsz v ≤ L := fun v hv => h v (by simp [hv])
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := ih ht
      calc HvdH.vsz a + (List.map HvdH.vsz t).sum ≤ L + t.length * L := add_le_add ha this
        _ = (t.length + 1) * L := by ring
  have hSx : (pool.map HvdH.vsz).sum ≤ 8 * L := by
    have := hsum pool hL
    rw [hlen] at this
    simpa using this
  have hgoal : K0 * (Bnd * ((Bnd * (pool.map HvdH.vsz).sum + 1) * (plan.length + 1))) + K0
      ≤ (2 * K0 + 1) * (Bnd * ((Bnd * (L + 1) * 8 + 1) * (plan.length + 1))) + (2 * K0 + 1) := by
    rcases Nat.eq_zero_or_pos Bnd with hB0 | hBp
    · subst hB0
      simp only [Nat.mul_zero, Nat.zero_mul, Nat.zero_add]
      omega
    · have hsumL : (pool.map HvdH.vsz).sum ≤ (L + 1) * 8 := by
        have := hSx; omega
      have hA : Bnd * (pool.map HvdH.vsz).sum + 1 ≤ Bnd * (L + 1) * 8 + 1 := by
        have h1 := Nat.mul_le_mul_left Bnd hsumL
        have h2 : Bnd * ((L + 1) * 8) = Bnd * (L + 1) * 8 := by ring
        omega
      have hK0 : K0 ≤ 2 * K0 + 1 := by omega
      have h3 : (Bnd * (pool.map HvdH.vsz).sum + 1) * (plan.length + 1)
          ≤ (Bnd * (L + 1) * 8 + 1) * (plan.length + 1) := Nat.mul_le_mul_right _ hA
      refine Nat.add_le_add ?_ hK0
      calc K0 * (Bnd * ((Bnd * (pool.map HvdH.vsz).sum + 1) * (plan.length + 1)))
          ≤ (2 * K0 + 1) * (Bnd * ((Bnd * (pool.map HvdH.vsz).sum + 1) * (plan.length + 1))) :=
            Nat.mul_le_mul_right _ hK0
        _ ≤ (2 * K0 + 1) * (Bnd * ((Bnd * (L + 1) * 8 + 1) * (plan.length + 1))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
  exact hgoal

end Work.MainP
