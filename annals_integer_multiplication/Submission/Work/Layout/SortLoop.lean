import Mathlib
import Submission.Work.Layout.SortDefs

set_option autoImplicit false

/-!
# The two-pass loop of the `sortByKey` program

Bookkeeping for the loop `while Y has a run: pass2`, which halves the number of runs (four times per
iteration) until a single sorted run remains.
-/

namespace Work.Layout
namespace Sk

open HvdH

/-- a configuration of the two run stacks: the runs of `X` and of `Y` -/
abbrev Cfg := List (List Val) × List (List Val)

/-- two merge passes on a configuration -/
def pass2P (c : Cfg) : Cfg := pass2R c.1 c.2

/-- the configuration after `i` iterations of the two-pass loop -/
def cfgI (c : Cfg) : ℕ → Cfg
  | 0 => c
  | i + 1 => pass2P (cfgI c i)

/-- the number of runs of a configuration -/
def cntC (c : Cfg) : ℕ := c.1.length + c.2.length

/-- the total size of the elements of a configuration -/
def totC (c : Cfg) : ℕ := ((c.1 ++ c.2).flatten.map vsz).sum + (c.1 ++ c.2).flatten.length

/-- the runs of a configuration are nonempty -/
def CfgNe (c : Cfg) : Prop := ∀ r ∈ c.1 ++ c.2, r ≠ []

/-- every element of a configuration is a record `cons (int k) v` with a natural key -/
def CfgRec (c : Cfg) : Prop :=
  ∀ v ∈ (c.1 ++ c.2).flatten, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v'

/-- every run of a configuration is strictly increasing -/
def CfgSort (c : Cfg) : Prop :=
  ∀ r ∈ c.1 ++ c.2, r.Pairwise (fun a b => pairKey a < pairKey b)

/-- the keys of a configuration are distinct -/
def CfgNd (c : Cfg) : Prop := (((c.1 ++ c.2).flatten).map pairKey).Nodup

/-- the length invariant between the two stacks -/
def CfgLen (c : Cfg) : Prop := c.1.length = c.2.length ∨ c.1.length = c.2.length + 1

/-- all the configuration invariants -/
def CfgOk (c : Cfg) : Prop := CfgNe c ∧ CfgRec c ∧ CfgSort c ∧ CfgNd c ∧ CfgLen c

/-- the configuration invariants together with "the elements are those of `L0`" -/
def CfgAll (L0 : List Val) (c : Cfg) : Prop := CfgOk c ∧ ((c.1 ++ c.2).flatten).Perm L0

/-- the state invariant of the loop: `X`,`Y` hold the runs `c`, every other stack is `S`, and the loop
flag `rF` is `cons` exactly when `Y` still holds a run -/
def LoopInv (X Y : Stk) (JX JY : List Glyph) (S : Stk → List Glyph) (s : State) (c : Cfg) : Prop :=
  s.stk X = runEncB c.1 ++ JX ∧ s.stk Y = runEncB c.2 ++ JY ∧
  (s.reg rF = Glyph.cons ↔ c.2 ≠ []) ∧
  (∀ k : Stk, k ≠ X → k ≠ Y → s.stk k = S k)

/-- one iteration of the two-pass loop: two passes and the re-peek of the loop flag -/
def loopBody (pLt pSz : Cmd) (X Y C D T1 T2 SA SB F1 F2 t d : Stk) : Cmd :=
  .seq (pass2 pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) (.peek Y rF)

theorem cfgI_succ (c : Cfg) (i : ℕ) : cfgI c (i + 1) = cfgI (pass2P c) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have h1 : cfgI c (i.succ + 1) = pass2P (cfgI c i.succ) := rfl
      have h2 : cfgI (pass2P c) i.succ = pass2P (cfgI (pass2P c) i) := rfl
      rw [h1, h2, ih]

/-- the loop stops once there is at most one run left -/
theorem CfgOk.nil_of_cnt_le_one {c : Cfg} (hok : CfgOk c) (hc : cntC c ≤ 1) : c.2 = [] := by
  obtain ⟨-, -, -, -, hlen⟩ := hok
  have hc' : c.1.length + c.2.length ≤ 1 := hc
  rcases hlen with hh | hh
  · exact List.eq_nil_of_length_eq_zero (by omega)
  · exact List.eq_nil_of_length_eq_zero (by omega)

/-- while at least two runs remain, `Y` still has a run -/
theorem CfgOk.ne_nil_of_two_le {c : Cfg} (hok : CfgOk c) (hc : 2 ≤ cntC c) : c.2 ≠ [] := by
  intro h
  obtain ⟨-, -, -, -, hlen⟩ := hok
  have hc' : 2 ≤ c.1.length + c.2.length := hc
  rcases hlen with hh | hh
  · have h1 : 1 ≤ c.2.length := by omega
    rw [h] at h1
    simp at h1
  · have h1 : 1 ≤ c.2.length := by omega
    rw [h] at h1
    simp at h1

/-- the arithmetic step of the loop bound: `4^(k+1)` runs are halved to at most `4^k` -/
theorem div_four_le (x k : ℕ) (h : x ≤ 4 ^ (k + 1)) : (x + 3) / 4 ≤ 4 ^ k := by
  have h2 : (x + 3) / 4 ≤ (4 ^ (k + 1) + 3) / 4 := Nat.div_le_div_right (by omega)
  have h3 : (4 ^ (k + 1) + 3) / 4 = 4 ^ k := by
    rw [pow_succ]
    omega
  omega

/-- the per-iteration cost telescopes -/
theorem loopCost (CB it' : ℕ) : CB + it' * (CB + 1) + 1 ≤ (it' + 1) * (CB + 1) := by
  have h : CB + it' * (CB + 1) + 1 = (it' + 1) * (CB + 1) := by ring
  omega

/-- **the two-pass loop**: from a configuration with `cntC c` runs and `cntC c ≤ 4^k`, the loop
performs at most `k` iterations and stops with at most one run left. -/
theorem loop_le {main : Cmd} {pLt pSz : Cmd} {X Y C D T1 T2 SA SB F1 F2 t d : Stk}
    {JX JY : List Glyph} {S : Stk → List Glyph} {CB : ℕ} {L0 : List Val}
    (hstep : ∀ (c : Cfg) (s : State), CfgAll L0 c → LoopInv X Y JX JY S s c → 2 ≤ cntC c →
      ∃ s', Ev main (loopBody pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) s s' CB ∧
        LoopInv X Y JX JY S s' (pass2P c) ∧ CfgAll L0 (pass2P c))
    (hdec : ∀ c : Cfg, CfgOk c → cntC (pass2P c) ≤ (cntC c + 3) / 4) :
    ∀ (k : ℕ) (c : Cfg) (s : State), CfgAll L0 c → LoopInv X Y JX JY S s c → cntC c ≤ 4 ^ k →
      ∃ (it : ℕ) (s' : State), it ≤ k ∧
        loopRuns main rF Glyph.cons (loopBody pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) it s s'
          (it * (CB + 1)) ∧
        LoopInv X Y JX JY S s' (cfgI c it) ∧ CfgAll L0 (cfgI c it) ∧ cntC (cfgI c it) ≤ 1 ∧
        s'.reg rF ≠ Glyph.cons := by
  intro k
  induction k with
  | zero =>
      intro c s hok hinv hc
      have hnil : c.2 = [] := CfgOk.nil_of_cnt_le_one hok.1 hc
      have hrf : s.reg rF ≠ Glyph.cons := fun h => (hinv.2.2.1).mp h hnil
      have hcnt : cntC (cfgI c 0) ≤ 1 := by
        show cntC c ≤ 1
        simpa [cntC, hnil] using hc
      exact ⟨0, s, Nat.zero_le _, by simpa using loopRuns.zero, hinv, hok, hcnt, hrf⟩
  | succ k ih =>
      intro c s hok hinv hc
      by_cases hsmall : cntC c ≤ 1
      · have hnil : c.2 = [] := CfgOk.nil_of_cnt_le_one hok.1 hsmall
        have hrf : s.reg rF ≠ Glyph.cons := fun h => (hinv.2.2.1).mp h hnil
        have hcnt : cntC (cfgI c 0) ≤ 1 := by
          show cntC c ≤ 1
          simpa [cntC, hnil] using hsmall
        exact ⟨0, s, Nat.zero_le _, by simpa using loopRuns.zero, hinv, hok, hcnt, hrf⟩
      · have htwo : 2 ≤ cntC c := by omega
        have hrf : s.reg rF = Glyph.cons :=
          (hinv.2.2.1).mpr (CfgOk.ne_nil_of_two_le hok.1 htwo)
        obtain ⟨s₁, hev, hinv₁, hok₁⟩ := hstep c s hok hinv htwo
        have hc₁ : cntC (pass2P c) ≤ 4 ^ k := by
          have h := hdec c hok.1
          have h2 := div_four_le (cntC c) k (by omega)
          omega
        obtain ⟨it', s₂, hit', hrun', hinv₂, hok₂, hcnt₂, hrf₂⟩ := ih (pass2P c) s₁ hok₁ hinv₁ hc₁
        have hcat : loopRuns main rF Glyph.cons (loopBody pLt pSz X Y C D T1 T2 SA SB F1 F2 t d)
            (it' + 1) s s₂ (CB + it' * (CB + 1) + 1) :=
          loopRuns.succ' hrf hev hrun' le_rfl
        have hcost : CB + it' * (CB + 1) + 1 ≤ (it' + 1) * (CB + 1) := loopCost CB it'
        have hinv₂' : LoopInv X Y JX JY S s₂ (cfgI c (it' + 1)) := by
          rw [cfgI_succ]; exact hinv₂
        have hok₂' : CfgAll L0 (cfgI c (it' + 1)) := by
          rw [cfgI_succ]; exact hok₂
        have hcnt₂' : cntC (cfgI c (it' + 1)) ≤ 1 := by
          rw [cfgI_succ]; exact hcnt₂
        exact ⟨it' + 1, s₂, by omega, loopRuns.mono (by omega) hcat hcost, hinv₂', hok₂', hcnt₂', hrf₂⟩

end Sk
end Work.Layout
