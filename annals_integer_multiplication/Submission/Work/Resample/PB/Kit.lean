import Mathlib
import Submission.Work.Resample.PB.Defs
import Submission.Work.Resample.PB.Pure

/-!
# `pbApplyAlong`: infrastructure for the phase lemmas

* `pushConstS_ev`, `pushMarkS_ev`, `pushNilS_ev`, `pushConsS_ev` — the tiny push programs;
* `prologue_ev`, `epilogue_ev` — pushing a boundary marker on / clearing a list of *distinct* stacks;
* `cntLoop_ev` — the generic counter loop `cntLoop`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.Resample.PB

open HvdH
open Work.Layout
open Work.Layout.AA

/-- monotonicity of `Nat.size` -/
theorem size_mono {a b : ℕ} (h : a ≤ b) : a.size ≤ b.size := Nat.size_le_size h

/-! ## 1. The tiny push programs -/

theorem pushConstS_ev (main : Cmd) (k : Stk) (c : Glyph) (r : Reg)
    (g : Reg → Glyph) (X : Stk → List Glyph) :
    ∃ s' n, Ev main (pushConstS k c r) ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk k = c :: X k ∧ (∀ j, j ≠ k → s'.stk j = X j) := by
  have h1 : Ev main (.set r c) ⟨g, X⟩ ⟨Function.update g r c, X⟩ 1 := ev_set' main r c g X
  have h2 : Ev main (.push k r) ⟨Function.update g r c, X⟩
      ⟨Function.update g r c, Function.update X k (c :: X k)⟩ 1 := by
    have h := ev_push' main k r (Function.update g r c) X
    rwa [Function.update_self] at h
  refine ⟨⟨Function.update g r c, Function.update X k (c :: X k)⟩, 2, ?_, by omega, ?_, ?_⟩
  · show Ev main (seqs [.set r c, .push k r]) _ _ 2
    exact Ev.seq' h1 h2 (by omega)
  · simp
  · intro j hj
    simp only [Function.update_of_ne hj]

theorem pushMarkS_ev (main : Cmd) (k : Stk) (r : Reg) (g : Reg → Glyph)
    (X : Stk → List Glyph) :
    ∃ s' n, Ev main (pushMarkS k r) ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk k = gMark :: X k ∧ (∀ j, j ≠ k → s'.stk j = X j) :=
  pushConstS_ev main k gMark r g X

theorem pushNilS_ev (main : Cmd) (k : Stk) (r : Reg) (g : Reg → Glyph)
    (X : Stk → List Glyph) :
    ∃ s' n, Ev main (pushNilS k r) ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.stk k = Glyph.nil :: X k ∧ (∀ j, j ≠ k → s'.stk j = X j) := by
  obtain ⟨s', n, h1, h2, h3, h4⟩ := pushGlyphs_ev main [Glyph.nil] k r g X
  refine ⟨s', n, h1, ?_, ?_, h4⟩
  · simp only [List.length_singleton] at h2; omega
  · rw [h3]; rfl

theorem pushConsS_ev (main : Cmd) (k : Stk) (r : Reg) (g : Reg → Glyph)
    (X : Stk → List Glyph) :
    ∃ s' n, Ev main (pushConsS k r) ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.stk k = Glyph.cons :: X k ∧ (∀ j, j ≠ k → s'.stk j = X j) := by
  obtain ⟨s', n, h1, h2, h3, h4⟩ := pushGlyphs_ev main [Glyph.cons] k r g X
  refine ⟨s', n, h1, ?_, ?_, h4⟩
  · simp only [List.length_singleton] at h2; omega
  · rw [h3]; rfl

/-! ## 2. Prologue and epilogue over a list of distinct stacks -/

theorem prologue_ev (main : Cmd) (ks : List Stk) (r : Reg) (hnd : ks.Nodup) :
    ∀ (g : Reg → Glyph) (X : Stk → List Glyph),
    ∃ s' n, Ev main (seqs (ks.map (fun k => pushMarkS k r))) ⟨g, X⟩ s' n ∧
      n ≤ 3 * ks.length + 1 ∧
      (∀ k, k ∈ ks → s'.stk k = gMark :: X k) ∧ (∀ k, k ∉ ks → s'.stk k = X k) := by
  induction ks with
  | nil =>
      intro g X
      refine ⟨⟨g, X⟩, 1, ?_, by omega, ?_, ?_⟩
      · simpa using Ev.seqs_nil (main := main) (s := (⟨g, X⟩ : State))
      · intro k hk; simp at hk
      · intro k _; rfl
  | cons a t ih =>
      intro g X
      obtain ⟨hna, hndt⟩ := List.nodup_cons.mp hnd
      simp only [List.map_cons]
      obtain ⟨s1, n1, h1, hn1, ha1, ht1⟩ := pushMarkS_ev main a r g X
      obtain ⟨s2, n2, h2, hn2, ha2, ht2⟩ := ih hndt s1.reg s1.stk
      refine ⟨s2, n1 + n2, Ev.seqs_cons h1 h2, ?_, ?_, ?_⟩
      · rw [List.length_cons]; omega
      · intro k hk
        by_cases hka : k = a
        · rw [hka, ht2 a hna, ha1]
        · have hkt : k ∈ t := by
            rcases List.mem_cons.mp hk with h | h
            · exact absurd h hka
            · exact h
          rw [ha2 k hkt, ht1 k hka]
      · intro k hk
        have hka : k ≠ a := fun h => hk (h ▸ List.mem_cons_self)
        have hkt : k ∉ t := fun h => hk (List.mem_cons_of_mem a h)
        rw [ht2 k hkt, ht1 k hka]

theorem epilogue_ev (main : Cmd) (ks : List Stk) (rr rf : Reg) (hrr : rr ≠ rf)
    (hnd : ks.Nodup) :
    ∀ (D Z : Stk → List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ k, k ∈ ks → X k = D k ++ gMark :: Z k) → (∀ k, k ∈ ks → gMark ∉ D k) →
      ∃ s' n, Ev main (seqs (ks.map (fun k => clearTo k rr rf))) ⟨g, X⟩ s' n ∧
        n ≤ 5 * (ks.map (fun k => (D k).length)).sum + 9 * ks.length + 1 ∧
        (∀ k, k ∈ ks → s'.stk k = Z k) ∧ (∀ k, k ∉ ks → s'.stk k = X k) := by
  induction ks with
  | nil =>
      intro D Z g X hX hD
      refine ⟨⟨g, X⟩, 1, ?_, by omega, ?_, ?_⟩
      · simpa using Ev.seqs_nil (main := main) (s := (⟨g, X⟩ : State))
      · intro k hk; simp at hk
      · intro k _; rfl
  | cons a t ih =>
      intro D Z g X hX hD
      obtain ⟨hna, hndt⟩ := List.nodup_cons.mp hnd
      simp only [List.map_cons]
      obtain ⟨s1, n1, h1, hn1, ha1, hta1⟩ :=
        clearTo_ev main a rr rf hrr g X (D a) (Z a) (hD a (by simp)) (hX a (by simp))
      obtain ⟨s2, n2, h2, hn2, ha2, ht2⟩ :=
        ih hndt D Z s1.reg s1.stk
          (fun k hk => (hta1 k (fun h => hna (h ▸ hk))).trans (hX k (List.mem_cons_of_mem a hk)))
          (fun k hk => hD k (List.mem_cons_of_mem a hk))
      refine ⟨s2, n1 + n2, Ev.seqs_cons h1 h2, ?_, ?_, ?_⟩
      · simp only [List.length_cons, List.sum_cons]
        omega
      · intro k hk
        by_cases hka : k = a
        · rw [hka, ht2 a hna, ha1]
        · have hkt : k ∈ t := by
            rcases List.mem_cons.mp hk with h | h
            · exact absurd h hka
            · exact h
          exact ha2 k hkt
      · intro k hk
        have hka : k ≠ a := fun h => hk (h ▸ List.mem_cons_self)
        have hkt : k ∉ t := fun h => hk (List.mem_cons_of_mem a h)
        rw [ht2 k hkt, hta1 k hka]

/-! ## 3. The generic counter loop -/

def cntLoop_body (c t : Stk) (body : Cmd) : Cmd :=
  seqs [isZeroInt c rC1 rL rC3,
        .ite rL Glyph.cons (.set rL Glyph.eos)
          (seqs [decInt c t rC1 rL rC3 rC4 rC5, body, .set rL Glyph.cons])]

/-- `cntLoop_key`: the loop runs `i` times when the counter on `c` holds `i`. -/
theorem cntLoop_key (main : Cmd) (c t : Stk) (body : Cmd) (hct : c ≠ t) (Bc : ℕ)
    (I : ℕ → (Stk → List Glyph) → Prop)
    (hctr : ∀ (i : ℕ) (X : Stk → List Glyph), I i X →
      ∃ D, X c = (Val.int (i : ℤ)).enc ++ gMark :: D)
    (hsc : ∀ (i : ℕ) (X : Stk → List Glyph), I i X → ∃ D, X t = gMark :: D)
    (hstep : ∀ (i : ℕ) (X : Stk → List Glyph) (g : Reg → Glyph), 1 ≤ i → I i X →
      ∃ s' n, Ev main (seqs [decInt c t rC1 rL rC3 rC4 rC5, body, .set rL Glyph.cons])
        ⟨g, X⟩ s' n ∧ n ≤ Bc ∧ I (i - 1) s'.stk ∧ s'.reg rL = Glyph.cons) :
    ∀ (i : ℕ) (g : Reg → Glyph) (X : Stk → List Glyph), g rL = Glyph.cons → I i X →
      ∃ s' C, loopRuns main rL Glyph.cons (cntLoop_body c t body) (i + 1) ⟨g, X⟩ s' C ∧
        C ≤ (i + 1) * (Bc + 12) + 20 ∧ I 0 s'.stk ∧ s'.reg rL = Glyph.eos := by
  intro i
  induction i with
  | zero =>
      intro g X hflag hI
      obtain ⟨D, hD⟩ := hctr 0 X hI
      obtain ⟨s1, n1, he1, hn1, hc1, hfr1, hfl1⟩ :=
        isZeroInt_ev main c rC1 rL rC3 (by decide) (by decide) (by decide) g X 0 (gMark :: D) hD
      have hs1r : s1.reg rL = Glyph.cons := hfl1.mp rfl
      have hXeq : s1.stk = X := by
        funext j
        by_cases hj : j = c
        · subst hj; rw [hc1, hD]
        · exact hfr1 j hj
      have hthen : Ev main (.set rL Glyph.eos) s1
          ⟨Function.update s1.reg rL Glyph.eos, s1.stk⟩ 1 := ev_set main rL Glyph.eos s1
      have hite : Ev main
          (.ite rL Glyph.cons (.set rL Glyph.eos)
            (seqs [decInt c t rC1 rL rC3 rC4 rC5, body, .set rL Glyph.cons])) s1
          ⟨Function.update s1.reg rL Glyph.eos, s1.stk⟩ 2 := Ev.iteT hs1r hthen
      have hbody : Ev main (cntLoop_body c t body) ⟨g, X⟩
          ⟨Function.update s1.reg rL Glyph.eos, s1.stk⟩ (n1 + 2) :=
        Ev.seq' he1 hite (by omega)
      refine ⟨_, n1 + 2 + 1, loopRuns.one hflag hbody, by omega, ?_, ?_⟩
      · rw [hXeq]; exact hI
      · simp
  | succ i ih =>
      intro g X hflag hI
      obtain ⟨D, hD⟩ := hctr (i + 1) X hI
      obtain ⟨s1, n1, he1, hn1, hc1, hfr1, hfl1⟩ :=
        isZeroInt_ev main c rC1 rL rC3 (by decide) (by decide) (by decide) g X (i + 1)
          (gMark :: D) hD
      have hr1 : s1.reg rL ≠ Glyph.cons := by
        intro hcon
        have := hfl1.mpr hcon
        omega
      have hXeq : s1.stk = X := by
        funext j
        by_cases hj : j = c
        · subst hj; rw [hc1, hD]
        · exact hfr1 j hj
      obtain ⟨s2, n2, he2, hn2, hI2, hr2⟩ := hstep (i + 1) X s1.reg (by omega) hI
      have he2' : Ev main (seqs [decInt c t rC1 rL rC3 rC4 rC5, body, .set rL Glyph.cons])
          ⟨s1.reg, s1.stk⟩ s2 n2 := by rw [hXeq]; exact he2
      have hite : Ev main
          (.ite rL Glyph.cons (.set rL Glyph.eos)
            (seqs [decInt c t rC1 rL rC3 rC4 rC5, body, .set rL Glyph.cons])) s1 s2
          (n2 + 1) := Ev.iteF hr1 he2'
      have hbody : Ev main (cntLoop_body c t body) ⟨g, X⟩ s2 (n1 + (n2 + 1)) :=
        Ev.seq' he1 hite (by omega)
      obtain ⟨s3, C3, hruns3, hC3, hI3, hr3⟩ := ih s2.reg s2.stk hr2 hI2
      have hcost : n1 + (n2 + 1) + C3 + 1 ≤ (i + 2) * (Bc + 12) + 20 := by
        have h1 := hn1
        have h2 := hn2
        have h3 := hC3
        have hexp : (i + 2) * (Bc + 12) = (i + 1) * (Bc + 12) + (Bc + 12) := by ring
        rw [hexp]
        omega
      have hle : (n1 + (n2 + 1)) + C3 + 1 ≤ n1 + (n2 + 1) + C3 + 1 := by omega
      exact ⟨s3, n1 + (n2 + 1) + C3 + 1,
        loopRuns.succ' hflag (hbody.mono (by omega)) hruns3 hle, hcost, hI3, hr3⟩

theorem cntLoop_ev (main : Cmd) (c t : Stk) (body : Cmd) (hct : c ≠ t) (Bc : ℕ)
    (I : ℕ → (Stk → List Glyph) → Prop)
    (hctr : ∀ (i : ℕ) (X : Stk → List Glyph), I i X →
      ∃ D, X c = (Val.int (i : ℤ)).enc ++ gMark :: D)
    (hsc : ∀ (i : ℕ) (X : Stk → List Glyph), I i X → ∃ D, X t = gMark :: D)
    (hstep : ∀ (i : ℕ) (X : Stk → List Glyph) (g : Reg → Glyph), 1 ≤ i → I i X →
      ∃ s' n, Ev main (seqs [decInt c t rC1 rL rC3 rC4 rC5, body, .set rL Glyph.cons])
        ⟨g, X⟩ s' n ∧ n ≤ Bc ∧ I (i - 1) s'.stk ∧ s'.reg rL = Glyph.cons)
    (k : ℕ) (g : Reg → Glyph) (X : Stk → List Glyph) (hI : I k X) :
    ∃ s' n, Ev main (cntLoop c t body) ⟨g, X⟩ s' n ∧
      n ≤ (k + 2) * (Bc + 12) + 22 ∧ I 0 s'.stk := by
  obtain ⟨s1, C1, hruns, hC1, hI0, hr1⟩ :=
    cntLoop_key main c t body hct Bc I hctr hsc hstep k
      (Function.update g rL Glyph.cons) X (by simp) hI
  have hset : Ev main (.set rL Glyph.cons) ⟨g, X⟩ ⟨Function.update g rL Glyph.cons, X⟩ 1 :=
    ev_set' main rL Glyph.cons g X
  have hloop : Ev main (.loop rL Glyph.cons (cntLoop_body c t body))
      ⟨Function.update g rL Glyph.cons, X⟩ s1 (C1 + 1) :=
    loopRuns.eval hruns (by rw [hr1]; decide)
  have hmain : Ev main (cntLoop c t body) ⟨g, X⟩ s1 (1 + (C1 + 1)) :=
    Ev.seq' hset hloop (by omega)
  refine ⟨s1, 1 + (C1 + 1), hmain, ?_, hI0⟩
  have hexp : (k + 2) * (Bc + 12) = (k + 1) * (Bc + 12) + (Bc + 12) := by ring
  rw [hexp]
  omega

end Work.Resample.PB
