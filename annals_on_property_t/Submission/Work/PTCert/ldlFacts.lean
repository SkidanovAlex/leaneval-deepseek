import Mathlib
import Submission.Work.PTCert.Glue3
import Submission.Work.PTCert.ldlAux
import Submission.Work.PTCert.ldlAux.foldStep_segs
import Submission.Work.PTCert.ldlAux.map_range_getD_drop
import Submission.Work.PTCert.ldlAux.blockRows4_getD_length
import Submission.Work.PTCert.ldlAux.foldStep_range_some

/-! Guidance from the project lead (the requester):

Context: `Submission/Work/PTCert/Glue2.lean` (concrete objects of the rank-5 certificate: EI, fE,
actE, actN, repE, nuE, Pmat, …, and the semantic Props ESem/TabSem/NSem/RowSem/GroupSem/OrbLabSem/
ClassSem/KleinSem = plain meanings of the kernel checks) and `Glue3.lean` (the Props of the
mathematical steps). READ BOTH FIRST, and `NOTES_LEAD_glue.md` (workspace root) for the whole chain.
Hypotheses of the form `CodeFacts`, `ConjActFacts`, `ActCSound`, `BitsBridge`, `OrbitDecomp`,
`KleinLevel`, `FourierTransport`, `LdlChainSound`, `WhtSound` are GlueDefs Props proved in parallel by
other agents; `ESem`… are data facts proved by kernel checks. Use them as given; do not re-prove them.
Already-proved theorems you may use directly: `Work.PTCert.avgMatInvariant`, `rowFormula`,
`twistedFourierCriterion`, `psdOfBlock`, `psdSignedPerm`, `labelPrinciple`, `avgPrinciple`, `gramSOS`,
`avgGram`, `ldlScaledPrinciple`, `letterAction`, `modelSound`, `sigmaGroupFacts` (+ namespace
SigmaFacts: signAut_mul, signAut_inv, sigAut_mul, sigAut_inv, mem_SigmaSet_iff, ...), `permCheckKSound`.
NEVER unfold the big data definitions (`eAll`, `eM`, …) or try `decide` on them: all data facts come
through the Sem hypotheses. Do not change Glue*.lean. If the statement is false, `declare_false`
with the concrete reason (and say which hypothesis is missing).
Apply `LdlChainSound` (hLC) once per ψ with n := nK k, B i j := if i ≤ j then kEntry rowTs k ψ i j else
kEntry rowTs k ψ j i (symmetric by construction), w i := (Ws.getD ψ []).getD i 1, C i := (Cs.getD ψ []).getD i [],
acc i := the ψ-th accumulator after processing rows < i.
The work: unroll `ldlSeg` (KernelCert.lean; structural recursion on the row list) over the segments: since
segs.flatten = List.range n, the rows are processed in order 0,1,…,n-1, and each processed row i runs
ldlRowStep for each ψ on (blockRows4 … i).getD ψ [] with weights (Ws ψ).getD i 1, (Ws ψ).drop i, C rows
(Cs ψ).getD i [], (Cs ψ).drop i, accumulator accs[ψ]. Define acc i by induction (the Option chain succeeds
at every row because every segment returns `some`). Then check that ldlRowStep's list arguments match
LdlChainSound's: (List.range (n - i)).map (fun d => B i (i + d)) = (blockRows4 … i).getD ψ [] — this needs the
LENGTH of the blockRow output list = n - i (= (ys.drop i).length, hypothesis on ys length) and entries
kEntry … i (i+d) (definition, i ≤ i + d); similarly (List.range (n-i)).map (w ∘ (i + ·)) = (Ws ψ).drop i
(length hypothesis) and for C.
-/

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ### One derived list fact used by the assembly below -/

/-- With `i = 0`: a list is the `range`-indexed list of its entries.  (Consequence of
`Work.PTCert.ldlAux.map_range_getD_drop`, proved by a colleague.) -/
private lemma map_range_getD_zero {α : Type} (l : List α) (a : α) :
    (List.range l.length).map (fun d => l.getD d a) = l := by
  simpa using ldlAux.map_range_getD_drop l a 0

/-! ### The main glue lemma -/

theorem ldlFacts (hLC : LdlChainSound) : LdlFacts := by
  intro rowTs k hk Cs Ws segs accs hflat haccs0 hseg hshape hyslen ψ hψ
  classical
  -- abbreviations
  set n := nK k with hn
  let g : ℕ → List (List ℤ) → Option (List (List ℤ)) :=
    ldlStepAll cmT eM repT repInfoT piIT piCodes rowTs (Sk k) (ksL.getD k []) (ysL.getD k []) Cs Ws
  let B : ℕ → ℕ → ℤ := fun i j => if i ≤ j then kEntry rowTs k ψ i j else kEntry rowTs k ψ j i
  let w : ℕ → ℤ := fun i => (Ws.getD ψ []).getD i 1
  let C : ℕ → List ℤ := fun i => (Cs.getD ψ []).getD i []
  let br : ℕ → List (List ℤ) := fun i =>
    blockRows4 cmT eM repT repInfoT piIT piCodes rowTs (Sk k) (ksL.getD k []) (ysL.getD k []) i
  let accn : ℕ → List (List ℤ) := fun i =>
    (foldStep g (List.range i) (accs 0)).getD (List.replicate 4 (List.replicate n 0))
  -- the shape hypotheses
  have hshape' := hshape ψ hψ
  have hWlen : (Ws.getD ψ []).length = n := hshape'.1
  have hClen : (Cs.getD ψ []).length = n := hshape'.2.1
  have hpos := hshape'.2.2
  have hys : (ysL.getD k []).length = n := hyslen
  -- `ldlSeg` is the fold of the row steps
  have hlSeg : ∀ is a, ldlSeg cmT eM repT repInfoT piIT piCodes rowTs (Sk k) (ksL.getD k [])
      (ysL.getD k []) Cs Ws is a = foldStep g is a :=
    fun is a => ldlSeg_eq_foldStep cmT eM repT repInfoT piIT piCodes rowTs (Sk k) (ksL.getD k [])
      (ysL.getD k []) Cs Ws is a
  -- the chain of segments, as a fold over `List.range n`
  have hchain : foldStep g (List.range n) (accs 0) = some (accs segs.length) := by
    rw [← hflat]
    exact ldlAux.foldStep_segs g segs accs (fun j hj => by rw [← hlSeg]; exact hseg j hj)
  have hsome : ∀ i ≤ n, ∃ Y, foldStep g (List.range i) (accs 0) = some Y :=
    ldlAux.foldStep_range_some g (accs 0) n hchain
  have haccn : ∀ i ≤ n, foldStep g (List.range i) (accs 0) = some (accn i) := by
    intro i hi
    obtain ⟨Y, hY⟩ := hsome i hi
    have hai : accn i = Y := by
      show (foldStep g (List.range i) (accs 0)).getD (List.replicate 4 (List.replicate n 0)) = Y
      rw [hY]
      rfl
    rw [hY, hai]
  -- one row step of the fold
  have hstepi : ∀ i < n, g i (accn i) = some (accn (i + 1)) := by
    intro i hi
    have h1 := haccn i (le_of_lt hi)
    have h2 := haccn (i + 1) (by omega)
    rw [foldStep_range_succ g i (accs 0)] at h2
    rw [h1, Option.bind_some] at h2
    exact h2
  -- the `ψ`-component of a successful step
  have hrow : ∀ i < n, ldlStep cmT eM repT repInfoT piIT piCodes rowTs (Sk k) (ksL.getD k [])
      (ysL.getD k []) Cs Ws i (accn i) ψ = some ((accn (i + 1)).getD ψ []) := by
    intro i hi
    obtain ⟨a, ha, hra⟩ := ldlStepAll_spec cmT eM repT repInfoT piIT piCodes rowTs (Sk k)
      (ksL.getD k []) (ysL.getD k []) Cs Ws i (accn i) (hstepi i hi) hψ
    rw [hra]
    exact ha
  refine hLC n B w C (fun i => (accn i).getD ψ []) ?_ ?_ ?_ ?_ ?_
  · -- symmetry of `B`
    intro i j
    show (if i ≤ j then kEntry rowTs k ψ i j else kEntry rowTs k ψ j i) =
      (if j ≤ i then kEntry rowTs k ψ j i else kEntry rowTs k ψ i j)
    by_cases h : i ≤ j
    · rw [if_pos h]
      by_cases h' : j ≤ i
      · rw [if_pos h']
        have hij : i = j := le_antisymm h h'
        subst hij
        rfl
      · rw [if_neg h']
    · rw [if_neg h, if_pos (by omega)]
  · -- positivity of the weights
    intro i hi
    exact (hpos i hi).1
  · -- length of the factor rows
    intro i hi
    exact (hpos i hi).2
  · -- the initial accumulator
    have h0 : accn 0 = accs 0 := by
      have hr : foldStep g (List.range 0) (accs 0) = some (accs 0) := by
        rw [List.range_eq_nil.mpr rfl]
        exact foldStep_nil_apply g (accs 0)
      show (foldStep g (List.range 0) (accs 0)).getD (List.replicate 4 (List.replicate n 0)) = accs 0
      rw [hr]
      rfl
    rw [h0, haccs0]
    exact List.getD_replicate _ hψ
  · -- the row steps
    intro i hi
    have hlen : ((br i).getD ψ []).length = n - i := by
      show ((blockRows4 cmT eM repT repInfoT piIT piCodes rowTs (Sk k) (ksL.getD k [])
        (ysL.getD k []) i).getD ψ []).length = n - i
      rw [ldlAux.blockRows4_getD_length cmT eM repT repInfoT piIT piCodes rowTs (Sk k) (ksL.getD k [])
        (ysL.getD k []) i ψ hψ, List.length_drop, hys]
    have hpt : ∀ d, B i (i + d) = ((br i).getD ψ []).getD d 0 := by
      intro d
      show (if i ≤ i + d then kEntry rowTs k ψ i (i + d) else kEntry rowTs k ψ (i + d) i) =
        ((br i).getD ψ []).getD d 0
      rw [if_pos (Nat.le_add_right i d)]
      show ((br i).getD ψ []).getD ((i + d) - i) 0 = ((br i).getD ψ []).getD d 0
      rw [Nat.add_sub_cancel_left]
    have hE1 : (List.range (n - i)).map (fun d => B i (i + d)) = (br i).getD ψ [] := by
      rw [← hlen]
      conv_rhs => rw [← map_range_getD_zero ((br i).getD ψ []) 0]
      apply List.map_congr_left
      intro d _
      exact hpt d
    have hE2 : (List.range (n - i)).map (fun d => w (i + d)) = (Ws.getD ψ []).drop i := by
      have h := ldlAux.map_range_getD_drop (Ws.getD ψ []) 1 i
      show (List.range (n - i)).map (fun d => (Ws.getD ψ []).getD (i + d) 1) =
        (Ws.getD ψ []).drop i
      rw [← hWlen]
      exact h
    have hE3 : (List.range (n - i)).map (fun d => C (i + d)) = (Cs.getD ψ []).drop i := by
      have h := ldlAux.map_range_getD_drop (Cs.getD ψ []) [] i
      show (List.range (n - i)).map (fun d => (Cs.getD ψ []).getD (i + d) []) =
        (Cs.getD ψ []).drop i
      rw [← hClen]
      exact h
    rw [hE1, hE2, hE3]
    show ldlRowStep ((br i).getD ψ []) ((Ws.getD ψ []).getD i 1) ((Ws.getD ψ []).drop i)
      ((Cs.getD ψ []).getD i []) ((Cs.getD ψ []).drop i) ((accn i).getD ψ []) =
      some ((accn (i + 1)).getD ψ [])
    exact hrow i hi

end Work.PTCert
