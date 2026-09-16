import Submission.CertFast
import Submission.CertIEval

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-!
# The `I`-form evaluated with the verified table

`Submission/CertIEval.lean` proves `certISum = certIval`, where `certIval` is the packed double
sum over the `272 × 272` signature-group pairs; `Submission.CertSsumAll.lean` proves that the
literal table `ssumTableL` is the packed row DP.  Here we rewrite `certIval` into `certIvalT`,
which evaluates the inner row lookup through the table `ssumTableL` and the contraction through
the shift-based `contPackS`.  The remaining step (`Submission/CertIArith.lean`) is then a single
`decide` on the resulting finite integer expression.
-/

namespace Commons.NumberTheory.MaynardSieve

/-! ## Auxiliary list lemmas -/

theorem zip_map_fst_eq {α β γ : Type*} (l : List α) (m : List β) (F : α → γ)
    (h : l.length ≤ m.length) : (l.zip m).map (fun q => F q.1) = l.map F := by
  induction l generalizing m with
  | nil => rfl
  | cons a t ih =>
      cases m with
      | nil => simp at h
      | cons b u =>
          rw [List.zip_cons_cons, List.map_cons, List.map_cons, ih u (by simpa using h)]

theorem mem_zip_map_self' {α β : Type*} {l : List α} {f : α → β} {q : α × β}
    (h : q ∈ l.zip (l.map f)) : q.2 = f q.1 := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
      rw [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
      rcases h with h | h
      · rw [h]
      · exact ih h

theorem zip_map_map_self' {α β γ : Type*} (l : List α) (f : α → β) (F : α → β → γ) :
    ((l.zip (l.map f)).map (fun r => F r.1 r.2)) = l.map (fun p => F p (f p)) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.cons.injEq, true_and, ih]

theorem zip_congr_left' {α β β' γ : Type*} (l : List α) (m : List β) (m' : List β')
    (F : α → γ) (h₁ : l.length ≤ m.length) (h₂ : l.length ≤ m'.length) :
    (l.zip m).map (fun q => F q.1) = (l.zip m').map (fun q => F q.1) := by
  rw [zip_map_fst_eq l m F h₁, zip_map_fst_eq l m' F h₂]

/-- The packed rows of the signature groups. -/
def cRows : List (List ℕ) := cSigs.map (fun p => packedRow (mult p.1))

theorem cRows_length : cRows.length = 272 := by
  rw [cRows, List.length_map, cSigs_length]

/-- The inner term of the `I`-contraction (packed form). -/
def termA (p p' : List ℕ × List ℤ) (val : ℕ) : ℤ :=
  contPack p.2 p'.2 (p.1.sum + p'.1.sum) * ((mc 50 (mult p'.1) * val : ℕ) : ℤ)

/-- The inner term of the `I`-contraction (shift-based form). -/
def termS (p p' : List ℕ × List ℤ) (val : ℕ) : ℤ :=
  contPackS p.2 p'.2 (p.1.sum + p'.1.sum) * ((mc 50 (mult p'.1) * val : ℕ) : ℤ)

/-- **The table-based evaluation of the `I`-form.** -/
def certIvalT : ℤ :=
  ((cSigs.zip ssumTableL).map (fun q =>
    ((cSigs.zip q.2).map (fun r => termS r.1 q.1 r.2)).sum)).sum

/-! ## The chain of rewrites -/

theorem certIval_eq_A : certIval
    = ((cSigs.zip cRows).map (fun q => (cSigs.map (fun p => termA p q.1 (unpack q.2 (mult p.1)))).sum)).sum := by
  unfold certIval termA cRows
  rfl

theorem A_eq_T1 : ((cSigs.zip cRows).map (fun q => (cSigs.map (fun p => termA p q.1 (unpack q.2 (mult p.1)))).sum)).sum
    = ((cSigs.zip cRows).map (fun q =>
        (cSigs.map (fun p => termA p q.1 (unpack (packedRow (mult q.1.1)) (mult p.1)))).sum)).sum := by
  refine congrArg List.sum (List.map_congr_left (fun q hq => ?_))
  refine congrArg List.sum (List.map_congr_left (fun p hp => ?_))
  rw [cRows] at hq
  rw [mem_zip_map_self' hq]

theorem T1_eq_T2 : ((cSigs.zip cRows).map (fun q =>
      (cSigs.map (fun p => termA p q.1 (unpack (packedRow (mult q.1.1)) (mult p.1)))).sum)).sum
    = ((cSigs.zip cRows).map (fun q =>
        ((cSigs.zip (cSigs.map (fun p => unpack (packedRow (mult q.1.1)) (mult p.1)))).map
          (fun r => termA r.1 q.1 r.2)).sum)).sum := by
  refine congrArg List.sum (List.map_congr_left (fun q hq => ?_))
  exact (congrArg List.sum (zip_map_map_self' cSigs
    (fun p => unpack (packedRow (mult q.1.1)) (mult p.1))
    (fun p val => termA p q.1 val))).symm

/-- The outer crop: the body is a function of `q.1` only, so the zipped row list may be replaced
by the table. -/
def outerBody (p' : List ℕ × List ℤ) : ℤ :=
  ((cSigs.zip (cSigs.map (fun p => unpack (packedRow (mult p'.1)) (mult p.1)))).map
    (fun r => termA r.1 p' r.2)).sum

theorem T2_eq_T3 : ((cSigs.zip cRows).map (fun q =>
      ((cSigs.zip (cSigs.map (fun p => unpack (packedRow (mult q.1.1)) (mult p.1)))).map
        (fun r => termA r.1 q.1 r.2)).sum)).sum
    = ((cSigs.zip ssumTableL).map (fun q =>
        ((cSigs.zip (cSigs.map (fun p => unpack (packedRow (mult q.1.1)) (mult p.1)))).map
          (fun r => termA r.1 q.1 r.2)).sum)).sum := by
  refine congrArg List.sum ?_
  exact zip_congr_left' cSigs cRows ssumTableL outerBody
    (by rw [cRows_length, cSigs_length]) (by rw [ssumTableL_length, cSigs_length])

theorem T3_eq_T4 : ((cSigs.zip ssumTableL).map (fun q =>
      ((cSigs.zip (cSigs.map (fun p => unpack (packedRow (mult q.1.1)) (mult p.1)))).map
        (fun r => termA r.1 q.1 r.2)).sum)).sum
    = ((cSigs.zip ssumTableL).map (fun q =>
        ((cSigs.zip q.2).map (fun r => termA r.1 q.1 r.2)).sum)).sum := by
  refine congrArg List.sum (List.map_congr_left (fun q hq => ?_))
  have hq' : cSigs.map (fun p => unpack (packedRow (mult q.1.1)) (mult p.1)) = q.2 := by
    rw [ssumTableL_mem hq]
    rfl
  rw [hq']

theorem T4_eq_T5 : ((cSigs.zip ssumTableL).map (fun q =>
      ((cSigs.zip q.2).map (fun r => termA r.1 q.1 r.2)).sum)).sum
    = ((cSigs.zip ssumTableL).map (fun q =>
        ((cSigs.zip q.2).map (fun r => termS r.1 q.1 r.2)).sum)).sum := by
  refine congrArg List.sum (List.map_congr_left (fun q hq => ?_))
  refine congrArg List.sum (List.map_congr_left (fun r hr => ?_))
  unfold termA termS
  rw [contPackS_eq r.1.2 q.1.2 (r.1.1.sum + q.1.1.sum) ?_]
  have h₁ : r.1.1 ∈ certGroupSigs := by
    rw [cSigs] at hr
    exact mem_cSigs_fst (mem_zip_fst hr)
  have h₂ : q.1.1 ∈ certGroupSigs := by
    rw [cSigs] at hq
    exact mem_cSigs_fst (mem_zip_fst hq)
  have e₁ := certGroupSigs_sum_le h₁
  have e₂ := certGroupSigs_sum_le h₂
  omega

theorem T5_eq_certIvalT : ((cSigs.zip ssumTableL).map (fun q =>
      ((cSigs.zip q.2).map (fun r => termS r.1 q.1 r.2)).sum)).sum = certIvalT := by
  unfold certIvalT
  rfl

/-- **`certIval` computed with the verified table.** -/
theorem certIval_eq_certIvalT : certIval = certIvalT :=
  (certIval_eq_A).trans (A_eq_T1.trans (T1_eq_T2.trans (T2_eq_T3.trans
    (T3_eq_T4.trans (T4_eq_T5.trans T5_eq_certIvalT)))))

/-- **`certISum` computed with the verified table.** -/
theorem certISum_eq_certIvalT : certISum = certIvalT :=
  (certISum_eq_certIval).trans certIval_eq_certIvalT

end Commons.NumberTheory.MaynardSieve
