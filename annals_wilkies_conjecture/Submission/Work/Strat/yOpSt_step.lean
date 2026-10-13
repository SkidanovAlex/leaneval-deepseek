import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.WilE5.Operators.opMono_step

/-!
# Stepping `yOpSt` at its smallest active fibre direction

`yOpSt c B m ψ` is the ordered iterate

`(detOpSt c B (q-1))^[m (q-1)] ⋯ (detOpSt c B 0)^[m 0] ψ`,

i.e. the `List.finRange q`-fold right fold of the one-step fibrewise operators `detOpSt c B l`
with multiplicities `m l` (so the operator with the *smallest* fibre direction sits outermost).

The statement proved here is the exact analogue of `opMono_step` for the fibrewise operator
`yOpSt`: if `l` is the *smallest* fibre direction carrying a nonzero multiplicity, the whole
iterate factors as `detOpSt c B l` applied to the iterate with the multiplicity of `l` decreased
by one.  The content is purely combinatorial in the abstract fold over `List.finRange q`.

The `private` fold helpers of `Submission.Work.WilE5.Operators.opMono_step` are not exported, so
the abstract recursion is repeated here for the `Fin q`-fold (there it is a `Fin k`-fold of
`detOp`, here a `Fin q`-fold of `detOpSt`).
-/

namespace Work.Strat

/-- The ordered iterate of the operators `g i` with multiplicities `m i` over `Fin k`, as a
right fold over `List.finRange k` (so index `0` is outermost). -/
private abbrev fr {α : Type*} (k : ℕ) (g : Fin k → α → α) (m : Fin k → ℕ) (f : α) : α :=
  (List.finRange k).foldr (fun i acc => (g i)^[m i] acc) f

/-- `Pi.single l 1` as an explicit function `Fin k → ℕ` (write `m - singleN l`). -/
private abbrev singleN {k : ℕ} (l : Fin k) : Fin k → ℕ := Pi.single l 1

/-- Peel the outermost index of `fr`: `List.finRange (n+1) = 0 :: (List.finRange n).map Fin.succ`. -/
private lemma fr_succ {α : Type*} (n : ℕ) (g : Fin (n+1) → α → α) (m : Fin (n+1) → ℕ) (f : α) :
    fr (n+1) g m f = (g 0)^[m 0] (fr n (fun i => g (Fin.succ i)) (fun i => m (Fin.succ i)) f) := by
  simp only [fr, List.finRange_succ, List.foldr_cons, List.foldr_map]

/-- `singleN` is compatible with `Fin.succ`. -/
private lemma singleN_succ {k : ℕ} (j i : Fin k) :
    singleN (Fin.succ j) (Fin.succ i) = singleN j i := by
  by_cases h : i = j
  · subst h; simp [singleN]
  · rw [singleN, singleN, Pi.single_eq_of_ne (fun hh => h (Fin.succ_inj.mp hh)),
      Pi.single_eq_of_ne h]

/-- The abstract fold recursion: the operator with the smallest index of nonzero multiplicity
sits outermost. -/
private lemma fr_step {α : Type*} (k : ℕ) (g : Fin k → α → α) (m : Fin k → ℕ) (f : α) (l : Fin k)
    (hm : m l ≠ 0) (hmin : ∀ l' : Fin k, m l' ≠ 0 → l ≤ l') :
    fr k g m f = g l (fr k g (m - singleN l) f) := by
  induction k with
  | zero => exact l.elim0
  | succ n ih =>
    rcases Fin.eq_zero_or_eq_succ l with h | ⟨j, h⟩
    · -- `l = 0`: all outer operators are missing, only the multiplicity of `0` decreases
      subst h
      have h0s : (fun i : Fin n => (m - singleN (0 : Fin (n+1))) (Fin.succ i))
          = fun i => m (Fin.succ i) := by
        funext i
        rw [Pi.sub_apply, singleN, Pi.single_eq_of_ne (Fin.succ_ne_zero i), Nat.sub_zero]
      have h00 : (m - singleN (0 : Fin (n+1))) 0 = m 0 - 1 := by
        rw [Pi.sub_apply, singleN, Pi.single_eq_same]
      rw [fr_succ n g m f, fr_succ n g (m - singleN (0:Fin (n+1))) f, h0s, h00]
      have hm0 : m 0 = (m 0 - 1) + 1 := by omega
      conv_lhs => rw [hm0]
      exact Function.iterate_succ_apply' (g 0) (m 0 - 1) _
    · -- `l = Fin.succ j`: index `0` carries multiplicity `0`, so reduce to the tail
      subst h
      have hm0 : m 0 = 0 := by
        by_contra hh
        have hle := hmin 0 hh
        rw [Fin.le_def] at hle
        simp only [Fin.val_succ, Fin.val_zero] at hle
        omega
      have hsingle : (fun i : Fin n => (m - singleN (Fin.succ j)) (Fin.succ i))
          = ((fun i : Fin n => m (Fin.succ i)) - singleN j) := by
        funext i
        simp only [Pi.sub_apply, singleN_succ]
      have hm'0 : (m - singleN (Fin.succ j)) 0 = 0 := by
        rw [Pi.sub_apply, singleN, Pi.single_eq_of_ne (Ne.symm (Fin.succ_ne_zero j)), Nat.sub_zero]
        exact hm0
      rw [fr_succ n g m f, fr_succ n g (m - singleN (Fin.succ j)) f, hsingle, hm'0, hm0]
      simp only [Function.iterate_zero_apply]
      have hmj : (fun i : Fin n => m (Fin.succ i)) j ≠ 0 := hm
      have hminj : ∀ l' : Fin n, (fun i : Fin n => m (Fin.succ i)) l' ≠ 0 → j ≤ l' := by
        intro l' h'
        have h2 := hmin (Fin.succ l') h'
        rwa [Fin.succ_le_succ_iff] at h2
      exact ih (fun i : Fin n => g (Fin.succ i)) (fun i : Fin n => m (Fin.succ i)) j hmj hminj

/-- **Stepping `yOpSt` at its smallest active fibre direction.** If `l` is the smallest fibre
direction with `m l ≠ 0`, the ordered iterate with multiplicities `m` is `detOpSt c B l`
composed with the iterate with the multiplicity of `l` decreased by one. -/
theorem yOpSt_step {p q r : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (B : List (WilkiesDesign.E.EAPoly (p + q) r × Fin q)) (m : Fin q → ℕ) (l : Fin q)
    (hm : m l ≠ 0) (hmin : ∀ l' : Fin q, m l' ≠ 0 → l ≤ l')
    (ψ : WilkiesDesign.E.EAPoly (p + q) r) :
    Work.WilE5.yOpSt c B m ψ = Work.WilE5.detOpSt c B l (Work.WilE5.yOpSt c B (Work.WilE5.mDec m l) ψ) := by
  have h := fr_step q (Work.WilE5.detOpSt c B) m ψ l hm hmin
  simpa only [Work.WilE5.yOpSt, fr, Work.WilE5.mDec, singleN] using h

end Work.Strat
