import Mathlib
import Submission.Work.Wilkies.E.Spec

/-!
# Stepping the ordered monomial operator `opMono`

`opMono c h ι m f` is the ordered iterate
`∂_{h,ι,k-1}^{m (k-1)} ⋯ ∂_{h,ι,0}^{m 0} f`, i.e. the `List.finRange k`-fold right fold of the
operators `detOp c h ι l` with multiplicities `m l` (so the operator with the *smallest* index
`l` is applied *last*, i.e. sits outermost).

The identity proved here says that if `l` is the *smallest* index carrying a nonzero
multiplicity, then the whole iterate factors as `detOp l` applied to the iterate with the
multiplicity of `l` decreased by one.  It is the elementary recursion that drives every
induction on the multiplicity vector `m`.

The mathematical content is purely combinatorial and lives entirely in the abstract fold
over `List.finRange k`; the two `private` helpers `fr`/`fr_step` isolate it from the
`MvPolynomial` layer.
-/

namespace Work.WilE5.Operators

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

/-- **Stepping `opMono` at its smallest active index.** If `l` is the smallest index with
`m l ≠ 0`, the ordered iterate with multiplicities `m` is `detOp l` composed with the iterate
with the multiplicity of `l` decreased by one. -/
theorem opMono_step {k r j : ℕ} (c : WilkiesDesign.E.EAChain k r) (h : Fin j → WilkiesDesign.E.EAPoly k r)
    (ι : Fin j → Fin k) (m : Fin k → ℕ) (f : WilkiesDesign.E.EAPoly k r) (l : Fin k)
    (hm : m l ≠ 0) (hmin : ∀ l' : Fin k, m l' ≠ 0 → l ≤ l') :
    WilkiesDesign.E.opMono c h ι m f =
      WilkiesDesign.E.detOp c h ι l (WilkiesDesign.E.opMono c h ι (m - Pi.single l 1) f) := by
  unfold WilkiesDesign.E.opMono
  exact fr_step k (fun i => WilkiesDesign.E.detOp c h ι i) m f l hm hmin

end Work.WilE5.Operators
