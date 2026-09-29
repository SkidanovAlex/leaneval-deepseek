import Mathlib
import Submission.Work.Fx.LogTwoDefs
import Submission.Work.Fx.LogTwoAux
import Submission.Work.Fx.LogTwoProg
import Submission.Work.Fx.LogTwoProg2
import Submission.Work.Fx.LogTwoMath

/-!
# The `log 2` word

Assembles the prologue, the `KernelLib` do-while loop (body from `LogTwoProg`) and the epilogue
into a single `Cmd` that maps the precision `p` to an integer `u` with `|u - 2^p log 2| ≤ 1`,
at cost polynomial in `p`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.Fx

open HvdH

/-- The window produced by one round of the loop body equals `WI (i+1)`. -/
theorem bodyWindow_eq (p i : ℕ) :
    ([.int (((logD p i : ℕ) : ℤ).tdiv 2),
      .int (((logS p i : ℕ) : ℤ) + ((((logD p i : ℕ) : ℤ).tdiv 2).tdiv ((i : ℤ) + 1))),
      .int ((i : ℤ) + 1), .int ((logM p : ℕ) : ℤ), .int (p : ℤ)] : List Val)
      = [.int ((logD p (i + 1) : ℕ) : ℤ), .int ((logS p (i + 1) : ℕ) : ℤ),
        .int ((i + 1 : ℕ) : ℤ), .int ((logM p : ℕ) : ℤ), .int (p : ℤ)] := by
  have hAc : (((logA p (i + 1) : ℕ) : ℤ)) = (((logD p (i + 1) : ℕ) : ℤ)).tdiv ((i : ℤ) + 1) := by
    rw [logA_cast p (i + 1),
      show (((i + 1 : ℕ)) : ℤ) = (i : ℤ) + 1 from by push_cast; ring]
  have h1 : (((logD p i : ℕ) : ℤ).tdiv 2) = (((logD p (i + 1) : ℕ) : ℤ)) := (logD_succ_Z p i).symm
  have h2 : (((logS p i : ℕ) : ℤ) + ((((logD p (i + 1) : ℕ) : ℤ)).tdiv ((i : ℤ) + 1)))
      = (((logS p (i + 1) : ℕ) : ℤ)) := by
    rw [← hAc, ← logS_succ_Z p i]
  have h3 : ((i : ℤ) + 1) = (((i + 1 : ℕ)) : ℤ) := (Nat.cast_add_one i).symm
  rw [h1, h2, h3]

theorem logTwoWord (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ), 100 ≤ p →
      HvdH.WordR main prog (fun vs => ∃ (rest : List HvdH.Val), vs = HvdH.Val.int (p : ℤ) :: rest)
        (fun vs out => ∃ (rest : List HvdH.Val) (u : ℤ), vs = HvdH.Val.int (p : ℤ) :: rest ∧
          out = HvdH.Val.int u :: rest ∧ |(u : ℝ) - 2 ^ p * Real.log 2| ≤ 1)
        (fun _ => K * (p + 1) ^ K) := by
  obtain ⟨cLoop, KLoop, hLoop⟩ := hk.loop
  obtain ⟨progPro, Kpro, hPro⟩ := logPrologueAux hk hi
  obtain ⟨progBody, Kbody, hBody⟩ := logBodyAux hk hi
  obtain ⟨progEpi, Kepi, hEpi⟩ := logEpilogueAux hk hi
  set Ktot : ℕ := Kpro + 23 * Kbody + 24 * KLoop + Kepi + 4 with hKtot
  refine ⟨.seq progPro (.seq (cLoop progBody) progEpi), Ktot, ?_⟩
  intro main p hp
  set cst : ℕ := Kbody * (p + 1) ^ 2 with hcst
  set WI : ℕ → List Val := fun i => [.int ((logD p i : ℕ) : ℤ), .int ((logS p i : ℕ) : ℤ),
      .int (i : ℤ), .int ((logM p : ℕ) : ℤ), .int (p : ℤ)] with hWI
  -- the loop, for a fixed ambient value tail `rest`
  have hloopRest : ∀ rest : List Val, WordR main (cLoop progBody)
      (fun vs => vs = WI 0 ++ rest) (fun _ out => out = WI (logM p + 1) ++ rest)
      (fun _ => (logM p + 1 + 1) * (cst + KLoop) + KLoop) := by
    intro rest
    have hbodyWord : ∀ i vs, (vs = WI i ++ rest ∧ i ≤ logM p) →
        WordR main progBody (fun w => w = vs)
          (fun _ out => ∃ vs', (out = .int 0 :: vs' ∧ vs' = WI (logM p + 1) ++ rest) ∨
            (out = .int 1 :: vs' ∧ ((vs' = WI (i + 1) ++ rest ∧ i + 1 ≤ logM p) ∧
              i + 1 < logM p + 1))) (fun _ => cst) := by
      intro i vs hIvs
      rcases hIvs with ⟨hvs, hile⟩
      have hspec := hBody main p ((logD p i : ℕ) : ℤ) ((logS p i : ℕ) : ℤ) (i : ℤ)
        ((logM p : ℕ) : ℤ) (p : ℤ) hp rfl (by positivity)
        (logD_isz_le p i) (logS_isz_le p i) (idx_isz_le p i (by omega)) (logM_isz_le p)
      -- the exact window produced by the body
      have h1 : WordR main progBody (fun w => w = vs)
          (fun _ out => ∃ o, out = o ++ rest ∧
            o = [.int (if (i : ℤ) < ((logM p : ℕ) : ℤ) then 1 else 0),
              .int (((logD p i : ℕ) : ℤ).tdiv 2),
              .int (((logS p i : ℕ) : ℤ) + ((((logD p i : ℕ) : ℤ).tdiv 2).tdiv ((i : ℤ) + 1))),
              .int ((i : ℤ) + 1), .int ((logM p : ℕ) : ℤ), .int (p : ℤ)]) (fun _ => cst) := by
        have h2 : WordR main progBody (fun w => w = WI i ++ rest)
            (fun _ out => ∃ o, out = o ++ rest ∧
              o = [.int (if (i : ℤ) < ((logM p : ℕ) : ℤ) then 1 else 0),
                .int (((logD p i : ℕ) : ℤ).tdiv 2),
                .int (((logS p i : ℕ) : ℤ) + ((((logD p i : ℕ) : ℤ).tdiv 2).tdiv ((i : ℤ) + 1))),
                .int ((i : ℤ) + 1), .int ((logM p : ℕ) : ℤ), .int (p : ℤ)])
            (fun _ => Kbody * (p + 1) ^ 2) :=
          hspec (WI i) rest (by simp [hWI]) (by simp only [hWI])
        refine hk.conseq (main := main) (p := progBody) (P := fun w => w = WI i ++ rest)
          (Q := fun _ out => ∃ o, out = o ++ rest ∧
            o = [.int (if (i : ℤ) < ((logM p : ℕ) : ℤ) then 1 else 0),
              .int (((logD p i : ℕ) : ℤ).tdiv 2),
              .int (((logS p i : ℕ) : ℤ) + ((((logD p i : ℕ) : ℤ).tdiv 2).tdiv ((i : ℤ) + 1))),
              .int ((i : ℤ) + 1), .int ((logM p : ℕ) : ℤ), .int (p : ℤ)])
          (C := fun _ => Kbody * (p + 1) ^ 2) (P' := fun w => w = vs)
          (Q' := fun _ out => ∃ o, out = o ++ rest ∧
            o = [.int (if (i : ℤ) < ((logM p : ℕ) : ℤ) then 1 else 0),
              .int (((logD p i : ℕ) : ℤ).tdiv 2),
              .int (((logS p i : ℕ) : ℤ) + ((((logD p i : ℕ) : ℤ).tdiv 2).tdiv ((i : ℤ) + 1))),
              .int ((i : ℤ) + 1), .int ((logM p : ℕ) : ℤ), .int (p : ℤ)])
          (C' := fun _ => cst) h2 ?_ ?_ ?_
        · intro w hw
          rw [hw, hvs]
        · intro w out hw hQ
          exact hQ
        · intro w hw
          rw [hcst]
      -- the list produced after the flag
      have huniv : ([.int (((logD p i : ℕ) : ℤ).tdiv 2),
            .int (((logS p i : ℕ) : ℤ) + ((((logD p i : ℕ) : ℤ).tdiv 2).tdiv ((i : ℤ) + 1))),
            .int ((i : ℤ) + 1), .int ((logM p : ℕ) : ℤ), .int (p : ℤ)] : List Val) ++ rest
          = WI (i + 1) ++ rest := by
        rw [hWI, bodyWindow_eq]
      refine hk.conseq (main := main) (p := progBody) (P := fun w => w = vs)
        (Q := fun _ out => ∃ o, out = o ++ rest ∧
          o = [.int (if (i : ℤ) < ((logM p : ℕ) : ℤ) then 1 else 0),
            .int (((logD p i : ℕ) : ℤ).tdiv 2),
            .int (((logS p i : ℕ) : ℤ) + ((((logD p i : ℕ) : ℤ).tdiv 2).tdiv ((i : ℤ) + 1))),
            .int ((i : ℤ) + 1), .int ((logM p : ℕ) : ℤ), .int (p : ℤ)])
        (C := fun _ => cst) (P' := fun w => w = vs)
        (Q' := fun _ out => ∃ vs', (out = .int 0 :: vs' ∧ vs' = WI (logM p + 1) ++ rest) ∨
          (out = .int 1 :: vs' ∧ ((vs' = WI (i + 1) ++ rest ∧ i + 1 ≤ logM p) ∧
            i + 1 < logM p + 1)))
        (C' := fun _ => cst) h1 (fun w hw => hw) ?_ (fun w hw => le_rfl)
      intro w out hw hQ
      rcases hQ with ⟨o, hout, ho⟩
      by_cases hlt : i < logM p
      · let VS : List Val := ([.int (((logD p i : ℕ) : ℤ).tdiv 2),
            .int (((logS p i : ℕ) : ℤ) + ((((logD p i : ℕ) : ℤ).tdiv 2).tdiv ((i : ℤ) + 1))),
            .int ((i : ℤ) + 1), .int ((logM p : ℕ) : ℤ), .int (p : ℤ)] : List Val) ++ rest
        refine ⟨VS, Or.inr ?_⟩
        constructor
        · rw [hout, ho]
          have hfl : (if (i : ℤ) < ((logM p : ℕ) : ℤ) then (1 : ℤ) else 0) = 1 := by
            rw [if_pos (by exact_mod_cast hlt)]
          simp only [hfl, List.cons_append, List.nil_append, VS]
        · constructor
          · constructor
            · simp only [VS]
              exact huniv
            · omega
          · omega
      · have hi : i = logM p := by omega
        let VS : List Val := ([.int (((logD p i : ℕ) : ℤ).tdiv 2),
            .int (((logS p i : ℕ) : ℤ) + ((((logD p i : ℕ) : ℤ).tdiv 2).tdiv ((i : ℤ) + 1))),
            .int ((i : ℤ) + 1), .int ((logM p : ℕ) : ℤ), .int (p : ℤ)] : List Val) ++ rest
        refine ⟨VS, Or.inl ?_⟩
        constructor
        · rw [hout, ho]
          have hneg : ¬ ((i : ℤ) < ((logM p : ℕ) : ℤ)) := by
            intro hc
            exact hlt (by exact_mod_cast hc)
          have hfl : (if (i : ℤ) < ((logM p : ℕ) : ℤ) then (1 : ℤ) else 0) = 0 := by
            rw [if_neg hneg]
          simp only [hfl, List.cons_append, List.nil_append, VS]
        · simp only [VS]
          rw [huniv, hi]
    refine hk.conseq (main := main) (p := cLoop progBody)
      (P := fun vs => vs = WI 0 ++ rest ∧ 0 ≤ logM p)
      (Q := fun _ out => out = WI (logM p + 1) ++ rest)
      (C := fun _ => (logM p + 1 + 1) * (cst + KLoop) + KLoop)
      (P' := fun vs => vs = WI 0 ++ rest)
      (Q' := fun _ out => out = WI (logM p + 1) ++ rest)
      (C' := fun _ => (logM p + 1 + 1) * (cst + KLoop) + KLoop)
      (hLoop main progBody (fun i vs => vs = WI i ++ rest ∧ i ≤ logM p)
        (fun out => out = WI (logM p + 1) ++ rest) cst (logM p + 1) hbodyWord)
      ?_ ?_ ?_
    · intro vs h
      exact ⟨h, by omega⟩
    · intro vs out h hQ
      exact hQ
    · intro vs h
      exact le_rfl
  -- the epilogue applies to the final loop window
  have hepiRest : ∀ rest : List Val, WordR main progEpi
      (fun vs => vs = WI (logM p + 1) ++ rest)
      (fun _ out => ∃ o, out = o ++ rest ∧ o = [.int ((logU p : ℕ) : ℤ)])
      (fun _ => Kepi * (p + 1) ^ 2) := by
    intro rest
    have hspec := hEpi main p ((logD p (logM p + 1) : ℕ) : ℤ) ((logS p (logM p + 1) : ℕ) : ℤ)
      ((logM p + 1 : ℕ) : ℤ) ((logM p : ℕ) : ℤ) hp rfl
      (logD_isz_le p (logM p + 1)) (logS_isz_le p (logM p + 1))
      (idx_isz_le p (logM p + 1) (by omega)) (logM_isz_le p)
    exact hspec (WI (logM p + 1)) rest (by simp [hWI]) (by simp only [hWI])
  -- assembly
  intro vs hvs s R hR
  rcases hvs with ⟨rest, hvs⟩
  obtain ⟨out1, s1, n1, ⟨o1, hout1, ho1⟩, hev1, hn1, hstk1, hoth1⟩ :=
    (hPro main p hp) [.int (p : ℤ)] rest (by simp) rfl ([.int (p : ℤ)] ++ rest) rfl s R
      (by rw [List.cons_append, List.nil_append, ← hvs]; exact hR)
  have hI0 : out1 = WI 0 ++ rest := by
    simp [hout1, ho1, hWI]
  obtain ⟨out2, s2, n2, hF2, hev2, hn2, hstk2, hoth2⟩ := hloopRest rest out1 hI0 s1 R hstk1
  obtain ⟨out3, s3, n3, ⟨o3, hout3, ho3⟩, hev3, hn3, hstk3, hoth3⟩ :=
    hepiRest rest out2 hF2 s2 R hstk2
  refine ⟨out3, s3, n1 + (n2 + n3), ⟨rest, ((logU p : ℕ) : ℤ), by rw [hvs], ?_, ?_⟩,
    Eval.seq hev1 (Eval.seq hev2 hev3), ?_, hstk3, ?_⟩
  · simp only [hout3, ho3, List.cons_append, List.nil_append]
  · simpa using logMainBoundAux p hp
  · -- cost
    have hp1 : 1 ≤ p + 1 := by omega
    have hsq : 1 ≤ (p + 1) ^ 2 := by simpa using Nat.pow_le_pow_left hp1 2
    have hcb : 1 ≤ (p + 1) ^ 3 := by simpa using Nat.pow_le_pow_left hp1 3
    have h23 : (p + 1) ^ 2 ≤ (p + 1) ^ 3 := by
      calc (p + 1) ^ 2 = (p + 1) ^ 2 * 1 := by ring
        _ ≤ (p + 1) ^ 2 * (p + 1) := Nat.mul_le_mul_left _ hp1
        _ = (p + 1) ^ 3 := by ring
    have h13 : (p + 1) ^ 3 ≤ (p + 1) ^ Ktot := Nat.pow_le_pow_right hp1 (by simp only [Ktot]; omega)
    have hl2 : logM p + 2 ≤ 23 * (p + 1) := by simp only [logM]; omega
    have hKl : KLoop ≤ KLoop * (p + 1) ^ 2 := by
      calc KLoop = KLoop * 1 := by ring
        _ ≤ KLoop * (p + 1) ^ 2 := Nat.mul_le_mul_left _ hsq
    have hKl3 : KLoop ≤ KLoop * (p + 1) ^ 3 := by
      calc KLoop = KLoop * 1 := by ring
        _ ≤ KLoop * (p + 1) ^ 3 := Nat.mul_le_mul_left _ hcb
    have h2a : cst + KLoop ≤ (Kbody + KLoop) * (p + 1) ^ 2 := by
      rw [hcst]
      have h9 : (Kbody + KLoop) * (p + 1) ^ 2 = Kbody * (p + 1) ^ 2 + KLoop * (p + 1) ^ 2 := by ring
      rw [h9]
      exact Nat.add_le_add_left hKl _
    have h2e : n2 ≤ (23 * Kbody + 24 * KLoop) * (p + 1) ^ 3 := by
      have h0 : n2 ≤ (logM p + 2) * (cst + KLoop) + KLoop := by
        have h := hn2
        simp only [Nat.add_assoc] at h
        exact h
      have h2b : (logM p + 2) * (cst + KLoop) ≤ 23 * (Kbody + KLoop) * (p + 1) ^ 3 :=
        calc (logM p + 2) * (cst + KLoop) ≤ (23 * (p + 1)) * ((Kbody + KLoop) * (p + 1) ^ 2) :=
              Nat.mul_le_mul hl2 h2a
          _ = 23 * (Kbody + KLoop) * (p + 1) ^ 3 := by ring
      have h2c : 23 * (Kbody + KLoop) * (p + 1) ^ 3 + KLoop
          ≤ (23 * Kbody + 24 * KLoop) * (p + 1) ^ 3 := by
        calc 23 * (Kbody + KLoop) * (p + 1) ^ 3 + KLoop
            ≤ 23 * (Kbody + KLoop) * (p + 1) ^ 3 + KLoop * (p + 1) ^ 3 :=
              Nat.add_le_add_left hKl3 _
          _ = (23 * Kbody + 24 * KLoop) * (p + 1) ^ 3 := by ring
      have h2b' : n2 ≤ 23 * (Kbody + KLoop) * (p + 1) ^ 3 + KLoop :=
        le_trans h0 (Nat.add_le_add_right h2b KLoop)
      exact le_trans h2b' h2c
    have h1e : n1 ≤ Kpro * (p + 1) ^ 3 := le_trans hn1 (Nat.mul_le_mul_left _ h23)
    have h3e : n3 ≤ Kepi * (p + 1) ^ 3 := le_trans hn3 (Nat.mul_le_mul_left _ h23)
    have hKc : Kpro + 23 * Kbody + 24 * KLoop + Kepi ≤ Ktot := by
      simp only [Ktot]; omega
    calc n1 + (n2 + n3) ≤ Kpro * (p + 1) ^ 3 + ((23 * Kbody + 24 * KLoop) * (p + 1) ^ 3
            + Kepi * (p + 1) ^ 3) := by
          exact Nat.add_le_add h1e (Nat.add_le_add h2e h3e)
      _ = (Kpro + 23 * Kbody + 24 * KLoop + Kepi) * (p + 1) ^ 3 := by ring
      _ ≤ Ktot * (p + 1) ^ 3 := Nat.mul_le_mul_right _ hKc
      _ ≤ Ktot * (p + 1) ^ Ktot := Nat.mul_le_mul_left _ h13
  · intro k hk'
    rw [hoth3 k hk', hoth2 k hk', hoth1 k hk']

end Work.Fx
