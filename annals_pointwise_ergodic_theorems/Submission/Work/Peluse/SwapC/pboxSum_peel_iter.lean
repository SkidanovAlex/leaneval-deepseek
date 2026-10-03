import Mathlib
import Submission.Work.Peluse.SwapC.pbox_peel
import Submission.Work.Peluse.Ulower.iterDelta_peel

/-!
# The iterated peel of the multiset box sum (KKL Proposition 6.2, "freeze the leaves")

Peeling the first `k` slots of `pboxSum (k + d) q₁ q₂ M S f` one after another leaves an average
over the `k` shift pairs of the level-`d` box sum of the iterated `Δ'`-difference
`Work.Peluse.SwapC.iterDeltaP`, with the normalisation multiplied by `((M^4)⁻¹)^k`
(`Work.Peluse.SwapC.pboxSum_peel_iter`).

The single peel is the workspace's `Work.Peluse.SwapC.pbox_peel`; iterating it `k` times needs two
plumbing facts:

* the peel supplies the successive `Δ'`-steps with the *first* shift pair applied innermost, while
  `iterDeltaP` applies the first pair outermost — the two conventions agree because `Δ'`-steps
  commute (`Work.Peluse.Ulower.iterDelta_peel`, i.e. `iterDeltaP_peel` below);
* the `Fin`-arithmetic `(k+1)+d = (k+d)+1` is not definitional, so the induction is run on
  coefficient tuples given as functions of the *value* (`fun i : Fin n => Q i.val`,
  `pboxSum_valrelabel`), and the general tuples are recovered at the end by extending them by `0`
  (`extFin`).

The induction step also reindexes the two outer shift sums of the right-hand side onto
`(m, m', H, H')` via `Fin.cons` (`sum_cons₂`), so that the induction hypothesis applies.
-/

set_option maxHeartbeats 1000000

open scoped BigOperators
open Work.Peluse.LadderP.Swap

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse

/-! ## The peel of a `Δ'`-step out of `iterDeltaP` -/

/-- `iterDeltaP` is the workspace's `Ulower.iterDelta'`. -/
private lemma iterDeltaP_eq_iterDelta' (k : ℕ) (sh : Fin k → ℤ × ℤ) (F : ℤ → ℂ) :
    Work.Peluse.SwapC.iterDeltaP k sh F = Work.Peluse.Ulower.iterDelta' k sh F := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.Peluse.SwapC.iterDeltaP_succ]
      rw [show Work.Peluse.Ulower.iterDelta' (k + 1) sh F = fun x =>
          star (Work.Peluse.Ulower.iterDelta' k (fun i => sh i.succ) F (x + (sh 0).1)) *
            Work.Peluse.Ulower.iterDelta' k (fun i => sh i.succ) F (x + (sh 0).2) from rfl]
      rw [ih]

/-- **The peel of the outermost shift pair**: the first `Δ'`-step of `iterDeltaP (k+1)` may be
moved to the innermost position, because the `Δ'`-steps commute. -/
private lemma iterDeltaP_peel (k : ℕ) (sh : Fin (k + 1) → ℤ × ℤ) (F : ℤ → ℂ) :
    Work.Peluse.SwapC.iterDeltaP (k + 1) sh F
      = Work.Peluse.SwapC.iterDeltaP k (fun i => sh i.succ)
          (Work.Peluse.DeltaP (sh 0).1 (sh 0).2 F) := by
  funext x
  rw [show Work.Peluse.SwapC.iterDeltaP (k + 1) sh F x
      = Work.Peluse.Ulower.iterDelta' (k + 1) sh F x from by rw [iterDeltaP_eq_iterDelta']]
  rw [Work.Peluse.Ulower.iterDelta_peel k sh F x]
  rw [show (fun w : ℤ => star (F (w + (sh 0).1)) * F (w + (sh 0).2))
      = Work.Peluse.DeltaP (sh 0).1 (sh 0).2 F from rfl]
  rw [show Work.Peluse.Ulower.iterDelta' k (fun i => sh i.succ)
        (Work.Peluse.DeltaP (sh 0).1 (sh 0).2 F) x
      = Work.Peluse.SwapC.iterDeltaP k (fun i => sh i.succ)
        (Work.Peluse.DeltaP (sh 0).1 (sh 0).2 F) x from by rw [iterDeltaP_eq_iterDelta']]

/-- **The peel at a `Fin.cons`-extended tuple of shifts**: this is the form in which the induction
step needs `iterDeltaP_peel`. -/
private lemma iterDeltaP_peel_cons {k M : ℕ} (Q₁ Q₂ : ℕ → ℤ) (m m' : Fin M × Fin M)
    (H H' : Fin k → Fin M × Fin M) (f : ℤ → ℂ) :
    Work.Peluse.SwapC.iterDeltaP (k + 1)
        (fun j : Fin (k + 1) =>
          (pdir (Q₁ j.val) (Q₂ j.val)
              ((Fin.cons (α := fun _ : Fin (k + 1) => Fin M × Fin M) m H) j),
           pdir (Q₁ j.val) (Q₂ j.val)
              ((Fin.cons (α := fun _ : Fin (k + 1) => Fin M × Fin M) m' H') j))) f
      = Work.Peluse.SwapC.iterDeltaP k
          (fun j : Fin k => (pdir (Q₁ (j.val + 1)) (Q₂ (j.val + 1)) (H j),
                             pdir (Q₁ (j.val + 1)) (Q₂ (j.val + 1)) (H' j)))
          (Work.Peluse.DeltaP (pdir (Q₁ 0) (Q₂ 0) m) (pdir (Q₁ 0) (Q₂ 0) m') f) := by
  let shC : Fin (k + 1) → ℤ × ℤ := fun j =>
    (pdir (Q₁ j.val) (Q₂ j.val) ((Fin.cons (α := fun _ : Fin (k + 1) => Fin M × Fin M) m H) j),
     pdir (Q₁ j.val) (Q₂ j.val) ((Fin.cons (α := fun _ : Fin (k + 1) => Fin M × Fin M) m' H') j))
  show Work.Peluse.SwapC.iterDeltaP (k + 1) shC f
      = Work.Peluse.SwapC.iterDeltaP k
          (fun j : Fin k => (pdir (Q₁ (j.val + 1)) (Q₂ (j.val + 1)) (H j),
                             pdir (Q₁ (j.val + 1)) (Q₂ (j.val + 1)) (H' j)))
          (Work.Peluse.DeltaP (pdir (Q₁ 0) (Q₂ 0) m) (pdir (Q₁ 0) (Q₂ 0) m') f)
  rw [iterDeltaP_peel k shC f]
  have hS : (fun i : Fin k => shC i.succ)
      = fun j : Fin k => (pdir (Q₁ (j.val + 1)) (Q₂ (j.val + 1)) (H j),
                          pdir (Q₁ (j.val + 1)) (Q₂ (j.val + 1)) (H' j)) := by
    funext j
    simp only [shC, Fin.cons_succ, Fin.val_succ]
  have hD : shC 0 = (pdir (Q₁ 0) (Q₂ 0) m, pdir (Q₁ 0) (Q₂ 0) m') := by
    simp only [shC, Fin.cons_zero, Fin.val_zero]
  rw [hS, hD]

/-! ## Relabelling the slot index type -/

/-- For coefficient tuples given as functions of the *value*, relabelling the slot index type along
an equality of the sizes does not change the box sum. -/
private lemma pboxSum_valrelabel {n m : ℕ} (h : n = m) (Q₁ Q₂ : ℕ → ℤ) (M : ℕ)
    (S : Finset ℤ) (f : ℤ → ℂ) :
    pboxSum n (fun i : Fin n => Q₁ i.val) (fun i : Fin n => Q₂ i.val) M S f
      = pboxSum m (fun i : Fin m => Q₁ i.val) (fun i : Fin m => Q₂ i.val) M S f := by
  subst h
  rfl

/-- The unique term of a sum over `Fin 0 → X`. -/
private lemma sum_fin_zero {X : Type} [Fintype X] (F : (Fin 0 → X) → ℂ) :
    (∑ h : Fin 0 → X, F h) = F (fun i => i.elim0) := by
  apply Finset.sum_eq_single
  · intro b _ hb
    exact absurd (funext fun i => i.elim0) hb
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The unique term of a double sum over `Fin 0 → X`. -/
private lemma sum_fin_zero₂ {X : Type} [Fintype X] (F : (Fin 0 → X) → (Fin 0 → X) → ℂ) :
    (∑ h : Fin 0 → X, ∑ h' : Fin 0 → X, F h h')
      = F (fun i => i.elim0) (fun i => i.elim0) := by
  rw [Finset.sum_congr rfl (fun h _ => sum_fin_zero (F h)), sum_fin_zero]

/-! ## Reindexing by `Fin.cons` -/

/-- Splitting a sum over `Fin (k+1) → X` into `X` times `Fin k → X`. -/
private lemma sum_cons_equiv' {k : ℕ} {X : Type} [Fintype X]
    (F : (Fin (k+1) → X) → ℂ) :
    ∑ h : Fin (k+1) → X, F h = ∑ m : X, ∑ hs : Fin k → X, F (Fin.cons m hs) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k+1) => X)) F]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun hs _ => ?_))
  congr 1

/-- The two shift-tuple sums reindexed onto `(m, m', H, H')`. -/
private lemma sum_cons₂ {k : ℕ} {X : Type} [Fintype X]
    (F : (Fin (k+1) → X) → (Fin (k+1) → X) → ℂ) :
    (∑ h : Fin (k+1) → X, ∑ h' : Fin (k+1) → X, F h h')
      = ∑ m : X, ∑ m' : X, ∑ H : Fin k → X, ∑ H' : Fin k → X,
          F (Fin.cons m H) (Fin.cons m' H') := by
  rw [sum_cons_equiv' (fun h => ∑ h' : Fin (k+1) → X, F h h')]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_congr rfl (fun H _ => sum_cons_equiv' (fun h' => F (Fin.cons m H) h'))]
  rw [Finset.sum_comm]

/-! ## The iterated peel, in value-indexed form -/

/-- **The iterated peel** for value-indexed coefficient tuples.  Peeling the first `k` slots of
`pboxSum (k+d)` leaves the level-`d` box sum of the iterated `Δ'`-difference, normalised by
`((M^4)⁻¹)^k`.

The proof is the induction on `k`: the base case is the (unique) empty shift pair, and the step
peels the first slot with `pbox_peel`, reindexes the right-hand side's shift sums onto
`(m, m', H, H')` (`sum_cons₂`), applies the induction hypothesis with the shifted coefficient
sequences `v ↦ Q (v+1)`, and reassembles the `Δ'`-steps with `iterDeltaP_peel_cons`. -/
private lemma peel_aux_val (k : ℕ) : ∀ (d : ℕ) (Q₁ Q₂ : ℕ → ℤ) (M : ℕ) (S : Finset ℤ)
    (f : ℤ → ℂ),
    pboxSum (k + d) (fun i : Fin (k + d) => Q₁ i.val) (fun i : Fin (k + d) => Q₂ i.val) M S f
      = (((M : ℂ) ^ 4)⁻¹) ^ k *
        ∑ h : Fin k → Fin M × Fin M, ∑ h' : Fin k → Fin M × Fin M,
          pboxSum d (fun i : Fin d => Q₁ (k + i.val)) (fun i : Fin d => Q₂ (k + i.val)) M S
            (Work.Peluse.SwapC.iterDeltaP k
              (fun j : Fin k => (pdir (Q₁ j.val) (Q₂ j.val) (h j),
                                 pdir (Q₁ j.val) (Q₂ j.val) (h' j))) f) := by
  induction k with
  | zero =>
      intro d Q₁ Q₂ M S f
      rw [pow_zero, one_mul]
      rw [show (∑ h : Fin 0 → Fin M × Fin M, ∑ h' : Fin 0 → Fin M × Fin M,
            pboxSum d (fun i : Fin d => Q₁ (0 + i.val)) (fun i : Fin d => Q₂ (0 + i.val)) M S
              (Work.Peluse.SwapC.iterDeltaP 0
                (fun j : Fin 0 => (pdir (Q₁ j.val) (Q₂ j.val) (h j),
                                   pdir (Q₁ j.val) (Q₂ j.val) (h' j))) f))
          = pboxSum d (fun i : Fin d => Q₁ (0 + i.val))
              (fun i : Fin d => Q₂ (0 + i.val)) M S f from by
        rw [sum_fin_zero₂]
        rfl]
      rw [pboxSum_valrelabel (show 0 + d = d by omega)]
      congr 1
      · funext i
        exact congrArg Q₁ (by simp)
      · funext i
        exact congrArg Q₂ (by simp)
  | succ k ih =>
      intro d Q₁ Q₂ M S f
      -- reindex the two outer shift sums of the right-hand side onto `(m, m', H, H')`
      rw [sum_cons₂ (F := fun (h h' : Fin (k + 1) → Fin M × Fin M) =>
            pboxSum d (fun i : Fin d => Q₁ ((k + 1) + i.val))
              (fun i : Fin d => Q₂ ((k + 1) + i.val)) M S
              (Work.Peluse.SwapC.iterDeltaP (k + 1)
                (fun j : Fin (k + 1) =>
                  (pdir (Q₁ j.val) (Q₂ j.val) (h j),
                   pdir (Q₁ j.val) (Q₂ j.val) (h' j))) f))]
      rw [pboxSum_valrelabel (show (k + 1) + d = (k + d) + 1 by omega)]
      rw [Work.Peluse.SwapC.pbox_peel (k + d) (fun i : Fin ((k + d) + 1) => Q₁ i.val)
        (fun i : Fin ((k + d) + 1) => Q₂ i.val) M S f]
      simp only [Fin.val_succ, Fin.val_zero]
      have hP : ∀ m m' : Fin M × Fin M,
          pboxSum (k + d) (fun i : Fin (k + d) => Q₁ (i.val + 1))
              (fun i : Fin (k + d) => Q₂ (i.val + 1)) M S
              (Work.Peluse.DeltaP (pdir (Q₁ 0) (Q₂ 0) m) (pdir (Q₁ 0) (Q₂ 0) m') f)
            = (((M : ℂ) ^ 4)⁻¹) ^ k *
              ∑ H : Fin k → Fin M × Fin M, ∑ H' : Fin k → Fin M × Fin M,
                pboxSum d (fun i : Fin d => Q₁ (k + i.val + 1))
                  (fun i : Fin d => Q₂ (k + i.val + 1)) M S
                  (Work.Peluse.SwapC.iterDeltaP k
                    (fun j : Fin k => (pdir (Q₁ (j.val + 1)) (Q₂ (j.val + 1)) (H j),
                                       pdir (Q₁ (j.val + 1)) (Q₂ (j.val + 1)) (H' j)))
                    (Work.Peluse.DeltaP (pdir (Q₁ 0) (Q₂ 0) m)
                      (pdir (Q₁ 0) (Q₂ 0) m') f)) :=
        fun m m' => ih d (fun v => Q₁ (v + 1)) (fun v => Q₂ (v + 1)) M S _
      rw [Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun m' _ => hP m m'))]
      simp only [← Finset.mul_sum]
      have hPT : ∀ (m m' : Fin M × Fin M) (H H' : Fin k → Fin M × Fin M),
          pboxSum d (fun i : Fin d => Q₁ (k + i.val + 1)) (fun i : Fin d => Q₂ (k + i.val + 1))
              M S
              (Work.Peluse.SwapC.iterDeltaP k
                (fun j : Fin k => (pdir (Q₁ (j.val + 1)) (Q₂ (j.val + 1)) (H j),
                                   pdir (Q₁ (j.val + 1)) (Q₂ (j.val + 1)) (H' j)))
                (Work.Peluse.DeltaP (pdir (Q₁ 0) (Q₂ 0) m) (pdir (Q₁ 0) (Q₂ 0) m') f))
            = pboxSum d (fun i : Fin d => Q₁ ((k + 1) + i.val))
                (fun i : Fin d => Q₂ ((k + 1) + i.val)) M S
                (Work.Peluse.SwapC.iterDeltaP (k + 1)
                  (fun j : Fin (k + 1) =>
                    (pdir (Q₁ j.val) (Q₂ j.val)
                        ((Fin.cons m H : Fin (k + 1) → Fin M × Fin M) j),
                     pdir (Q₁ j.val) (Q₂ j.val)
                        ((Fin.cons m' H' : Fin (k + 1) → Fin M × Fin M) j))) f) := by
        intro m m' H H'
        rw [iterDeltaP_peel_cons (M := M) Q₁ Q₂ m m' H H' f]
        refine congrArg₂ (fun (A B : Fin d → ℤ) => pboxSum d A B M S
          (Work.Peluse.SwapC.iterDeltaP k
            (fun j : Fin k => (pdir (Q₁ (j.val + 1)) (Q₂ (j.val + 1)) (H j),
                               pdir (Q₁ (j.val + 1)) (Q₂ (j.val + 1)) (H' j)))
            (Work.Peluse.DeltaP (pdir (Q₁ 0) (Q₂ 0) m) (pdir (Q₁ 0) (Q₂ 0) m') f))) ?_ ?_
        · funext i
          exact congrArg Q₁ (by omega)
        · funext i
          exact congrArg Q₂ (by omega)
      rw [Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun m' _ =>
        Finset.sum_congr rfl (fun H _ => Finset.sum_congr rfl (fun H' _ => hPT m m' H H'))))]
      rw [pow_succ]
      ring

/-- Total extension of a tuple by `0`. -/
private def extFin {n : ℕ} (q : Fin n → ℤ) : ℕ → ℤ := fun v => if hv : v < n then q ⟨v, hv⟩ else 0

/-- `extFin` restricts to `q` on `Fin n`. -/
private lemma extFin_apply {n : ℕ} (q : Fin n → ℤ) (i : Fin n) : extFin q i.val = q i := by
  show (if hv : i.val < n then q ⟨i.val, hv⟩ else 0) = q i
  rw [dif_pos i.isLt]

/-- **Iterated peel.**  Peeling the first `k` slots one after another leaves an average over the
`k` shift pairs of the level-`d` box sum of the iterated `Δ'`-difference `iterDeltaP`, and multiplies
the normalisation by `((M^4)⁻¹)^k`.  This is the "freeze the other leaves into the function" step of
`concatAll` (KKL Proposition 6.2). -/
theorem pboxSum_peel_iter (k d : ℕ) (q₁ q₂ : Fin (k + d) → ℤ) (M : ℕ) (S : Finset ℤ)
    (f : ℤ → ℂ) :
    Work.Peluse.LadderP.Swap.pboxSum (k + d) q₁ q₂ M S f
      = (((M : ℂ) ^ 4)⁻¹) ^ k *
        ∑ h : Fin k → Fin M × Fin M, ∑ h' : Fin k → Fin M × Fin M,
          Work.Peluse.LadderP.Swap.pboxSum d (fun i => q₁ (Fin.natAdd k i))
            (fun i => q₂ (Fin.natAdd k i)) M S
            (Work.Peluse.SwapC.iterDeltaP k
              (fun j => (Work.Peluse.LadderP.Swap.pdir (q₁ (Fin.castAdd d j))
                            (q₂ (Fin.castAdd d j)) (h j),
                         Work.Peluse.LadderP.Swap.pdir (q₁ (Fin.castAdd d j))
                            (q₂ (Fin.castAdd d j)) (h' j))) f) := by
  have hPP : Work.Peluse.LadderP.Swap.pboxSum (k + d) q₁ q₂ M S f
      = Work.Peluse.LadderP.Swap.pboxSum (k + d) (fun i : Fin (k + d) => extFin q₁ i.val)
          (fun i : Fin (k + d) => extFin q₂ i.val) M S f := by
    refine congrArg₂ (fun (A B : Fin (k + d) → ℤ) =>
      Work.Peluse.LadderP.Swap.pboxSum (k + d) A B M S f) ?_ ?_
    · exact funext (fun i => (extFin_apply q₁ i).symm)
    · exact funext (fun i => (extFin_apply q₂ i).symm)
  have he₁ : ∀ j : Fin k, extFin q₁ j.val = q₁ (Fin.castAdd d j) := by
    intro j
    rw [← show (Fin.castAdd d j).val = j.val by simp]
    exact extFin_apply q₁ (Fin.castAdd d j)
  have he₂ : ∀ j : Fin k, extFin q₂ j.val = q₂ (Fin.castAdd d j) := by
    intro j
    rw [← show (Fin.castAdd d j).val = j.val by simp]
    exact extFin_apply q₂ (Fin.castAdd d j)
  have hcoef₁ : (fun i : Fin d => extFin q₁ (k + i.val))
      = (fun i : Fin d => q₁ (Fin.natAdd k i)) := by
    funext i
    rw [← show (Fin.natAdd k i).val = k + i.val by simp]
    exact extFin_apply q₁ (Fin.natAdd k i)
  have hcoef₂ : (fun i : Fin d => extFin q₂ (k + i.val))
      = (fun i : Fin d => q₂ (Fin.natAdd k i)) := by
    funext i
    rw [← show (Fin.natAdd k i).val = k + i.val by simp]
    exact extFin_apply q₂ (Fin.natAdd k i)
  have hST : (∑ h : Fin k → Fin M × Fin M, ∑ h' : Fin k → Fin M × Fin M,
        Work.Peluse.LadderP.Swap.pboxSum d (fun i : Fin d => extFin q₁ (k + i.val))
          (fun i : Fin d => extFin q₂ (k + i.val)) M S
          (Work.Peluse.SwapC.iterDeltaP k
            (fun j : Fin k => (Work.Peluse.LadderP.Swap.pdir (extFin q₁ j.val)
                                  (extFin q₂ j.val) (h j),
                               Work.Peluse.LadderP.Swap.pdir (extFin q₁ j.val)
                                  (extFin q₂ j.val) (h' j))) f))
      = ∑ h : Fin k → Fin M × Fin M, ∑ h' : Fin k → Fin M × Fin M,
        Work.Peluse.LadderP.Swap.pboxSum d (fun i : Fin d => q₁ (Fin.natAdd k i))
          (fun i : Fin d => q₂ (Fin.natAdd k i)) M S
          (Work.Peluse.SwapC.iterDeltaP k
            (fun j : Fin k => (Work.Peluse.LadderP.Swap.pdir (q₁ (Fin.castAdd d j))
                                  (q₂ (Fin.castAdd d j)) (h j),
                               Work.Peluse.LadderP.Swap.pdir (q₁ (Fin.castAdd d j))
                                  (q₂ (Fin.castAdd d j)) (h' j))) f) := by
    refine Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => ?_))
    have hsh : (fun j : Fin k => (Work.Peluse.LadderP.Swap.pdir (extFin q₁ j.val)
                                    (extFin q₂ j.val) (h j),
                                  Work.Peluse.LadderP.Swap.pdir (extFin q₁ j.val)
                                    (extFin q₂ j.val) (h' j)))
        = fun j : Fin k => (Work.Peluse.LadderP.Swap.pdir (q₁ (Fin.castAdd d j))
                              (q₂ (Fin.castAdd d j)) (h j),
                            Work.Peluse.LadderP.Swap.pdir (q₁ (Fin.castAdd d j))
                              (q₂ (Fin.castAdd d j)) (h' j)) := by
      funext j
      rw [he₁ j, he₂ j]
    have hiter : Work.Peluse.SwapC.iterDeltaP k
          (fun j : Fin k => (Work.Peluse.LadderP.Swap.pdir (extFin q₁ j.val)
                                (extFin q₂ j.val) (h j),
                             Work.Peluse.LadderP.Swap.pdir (extFin q₁ j.val)
                                (extFin q₂ j.val) (h' j))) f
        = Work.Peluse.SwapC.iterDeltaP k
          (fun j : Fin k => (Work.Peluse.LadderP.Swap.pdir (q₁ (Fin.castAdd d j))
                                (q₂ (Fin.castAdd d j)) (h j),
                             Work.Peluse.LadderP.Swap.pdir (q₁ (Fin.castAdd d j))
                                (q₂ (Fin.castAdd d j)) (h' j))) f :=
      congrArg (fun sh : Fin k → ℤ × ℤ => Work.Peluse.SwapC.iterDeltaP k sh f) hsh
    exact (congrArg₂ (fun (A B : Fin d → ℤ) => Work.Peluse.LadderP.Swap.pboxSum d A B M S
        (Work.Peluse.SwapC.iterDeltaP k
          (fun j : Fin k => (Work.Peluse.LadderP.Swap.pdir (extFin q₁ j.val)
                                (extFin q₂ j.val) (h j),
                             Work.Peluse.LadderP.Swap.pdir (extFin q₁ j.val)
                                (extFin q₂ j.val) (h' j))) f))
        hcoef₁ hcoef₂).trans
      (congrArg (fun G : ℤ → ℂ => Work.Peluse.LadderP.Swap.pboxSum d
        (fun i : Fin d => q₁ (Fin.natAdd k i)) (fun i : Fin d => q₂ (Fin.natAdd k i)) M S G)
        hiter)
  calc Work.Peluse.LadderP.Swap.pboxSum (k + d) q₁ q₂ M S f
      = Work.Peluse.LadderP.Swap.pboxSum (k + d) (fun i : Fin (k + d) => extFin q₁ i.val)
          (fun i : Fin (k + d) => extFin q₂ i.val) M S f := hPP
    _ = (((M : ℂ) ^ 4)⁻¹) ^ k *
        (∑ h : Fin k → Fin M × Fin M, ∑ h' : Fin k → Fin M × Fin M,
          Work.Peluse.LadderP.Swap.pboxSum d (fun i : Fin d => extFin q₁ (k + i.val))
            (fun i : Fin d => extFin q₂ (k + i.val)) M S
            (Work.Peluse.SwapC.iterDeltaP k
              (fun j : Fin k => (Work.Peluse.LadderP.Swap.pdir (extFin q₁ j.val)
                                    (extFin q₂ j.val) (h j),
                                 Work.Peluse.LadderP.Swap.pdir (extFin q₁ j.val)
                                    (extFin q₂ j.val) (h' j))) f)) :=
        peel_aux_val k d (extFin q₁) (extFin q₂) M S f
    _ = (((M : ℂ) ^ 4)⁻¹) ^ k *
        (∑ h : Fin k → Fin M × Fin M, ∑ h' : Fin k → Fin M × Fin M,
          Work.Peluse.LadderP.Swap.pboxSum d (fun i : Fin d => q₁ (Fin.natAdd k i))
            (fun i : Fin d => q₂ (Fin.natAdd k i)) M S
            (Work.Peluse.SwapC.iterDeltaP k
              (fun j : Fin k => (Work.Peluse.LadderP.Swap.pdir (q₁ (Fin.castAdd d j))
                                    (q₂ (Fin.castAdd d j)) (h j),
                                 Work.Peluse.LadderP.Swap.pdir (q₁ (Fin.castAdd d j))
                                    (q₂ (Fin.castAdd d j)) (h' j))) f)) := by
        rw [hST]

end

end Work.Peluse.SwapC
