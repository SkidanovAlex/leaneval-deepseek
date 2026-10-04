import Mathlib
import Submission.Work.Diff.EXT.evolX.ladderAtoms
import Submission.Work.Diff.GE.swap_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The packing identity: swapping two adjacent derivative slots of the tower

`Work.Diff.EXT.evolX.ckt_adjacent_swap_bound` bounds
`|ckt g d G x − ckt g d (tupSwap d p hp G) x|` by `C · Shape g x (d−2) · ∏ ‖G r x‖`.

The present module proves the *identity* behind it (`ckt_sub_tupSwap_eq`): the difference of the
level-`d` tower at a tuple and at its `(p, p+1)`-swap is (up to sign) the `p`-fold `extStep` of the
curvature action `curvActT g (d−2−p)`, i.e. the level drops to `d−2`.

The route is the Ricci identity in the form of `Work.Diff.GE.extD_sub_swap` (proved): if a
field-level tensor `τ` of arity `ι` satisfies `τ F − τ (F ∘ σ) = −τ' F` for every smooth tuple
`F` (with `σ` an involution), then the same identity holds for the `Ext`-derivatives
`extD cov τ`.  Since `extD (lcOf g) (ckt g m) x (G 0) (G ∘ succ) = ckt g (m+1) G x`
(`Work.Diff.EXT.extD_ckt`), one step of the induction on `p` is exactly one `extStep` of the
difference.  The base case `p = 0` is `Work.Diff.EXT.ckt_sub_swap`.

* `ladderStep g j i S` is the `i`-fold `extStep` of the operator `S` of arity `j+6`; the result has
  arity `(j+2+i)+4` — the arity is written in this "level" form so that the level-`(j+2+i)` tower
  and the iterate have literally the same index type;
* `sigPerm j i` is the transposition `(i, i+1)` on `Fin ((j+2+i)+4)`, which is the swap of the two
  slots `p`, `p+1` of the level-`(j+2+i)` tower once the outer `i` derivative slots are added.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

local macro "Tf" : term => `((y : M) → TangentSpace I y)

/-! ## The iterate of `extStep` in level form -/

/-- `ladderStep g j i S` is the `i`-fold `extStep` of an operator `S` of arity `j + 6`; the result
has arity `(j + 2 + i) + 4`, i.e. it is an operator at level `j + 2 + i`. -/
noncomputable def ladderStep (g : SMet I M) (j : ℕ) : ∀ i : ℕ,
    ((Fin (j + 6) → Tf) → M → ℝ) → ((Fin ((j + 2 + i) + 4) → Tf) → M → ℝ)
  | 0, S => S
  | i + 1, S => extStep (I := I) (M := M) g (ladderStep g j i S)

@[simp] theorem ladderStep_zero (g : SMet I M) (j : ℕ) (S : (Fin (j + 6) → Tf) → M → ℝ) :
    ladderStep (I := I) (M := M) g j 0 S = S := rfl

theorem ladderStep_succ (g : SMet I M) (j i : ℕ)
    (S : (Fin (j + 6) → Tf) → M → ℝ) :
    ladderStep (I := I) (M := M) g j (i + 1) S
      = extStep (I := I) (M := M) g (ladderStep (I := I) (M := M) g j i S) := rfl

/-! ## `extStep` is `extD` on the shifted tuple -/

/-- `extStep` is the `Ext`-derivative `extD` evaluated on the tuple whose head is the direction and
whose tail is the shifted tuple. -/
theorem extStep_eq_extD (g : SMet I M) {K : ℕ} (S : (Fin K → Tf) → M → ℝ)
    (F : Fin (K + 1) → Tf) (y : M) :
    extStep (I := I) (M := M) g S F y
      = Work.Diff.GE.extD (Submission.Diff.lcOf g) S y (F 0)
          (fun r : Fin K => F r.succ) := rfl

/-! ## The transposition `(i, i+1)` on `Fin ((j+2+i)+4)` -/

/-- The transposition `(i, i+1)` on `Fin ((j+2+i)+4)`: the swap of the two adjacent *derivative*
slots `i`, `i+1` of the level-`(j+2+i)` tower. -/
noncomputable def sigPerm (j i : ℕ) : Equiv.Perm (Fin ((j + 2 + i) + 4)) :=
  Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩

/-- The value of `sigPerm`. -/
theorem sigPerm_apply (j i : ℕ) (r : Fin ((j + 2 + i) + 4)) :
    sigPerm j i r = (if (r : ℕ) = i then (⟨i + 1, by omega⟩ : Fin ((j + 2 + i) + 4))
      else if (r : ℕ) = i + 1 then ⟨i, by omega⟩ else r) := by
  rw [sigPerm, Equiv.swap_apply_def]
  by_cases h1 : (r : ℕ) = i
  · rw [if_pos (show r = (⟨i, by omega⟩ : Fin ((j + 2 + i) + 4)) from Fin.ext h1), if_pos h1]
  · rw [if_neg (show ¬ (r = (⟨i, by omega⟩ : Fin ((j + 2 + i) + 4))) from fun h => h1 (by rw [h])),
      if_neg h1]
    by_cases h2 : (r : ℕ) = i + 1
    · rw [if_pos (show r = (⟨i + 1, by omega⟩ : Fin ((j + 2 + i) + 4)) from Fin.ext h2), if_pos h2]
    · rw [if_neg (show ¬ (r = (⟨i + 1, by omega⟩ : Fin ((j + 2 + i) + 4)))
          from fun h => h2 (by rw [h])), if_neg h2]

/-- `sigPerm` is an involution. -/
theorem sigPerm_invol (j i : ℕ) (r : Fin ((j + 2 + i) + 4)) :
    sigPerm j i (sigPerm j i r) = r :=
  (sigPerm j i).left_inv r

/-- The compatibility of the chain of transpositions with the shift of the tuple: the new
transposition acts on shifted indices as the old one. -/
theorem sigPerm_succ_succ (j i : ℕ) (r : Fin ((j + 2 + i) + 4)) :
    sigPerm j (i + 1) (Fin.succ r) = Fin.succ (sigPerm j i r) := by
  rw [sigPerm_apply (j := j) (i := i + 1) (r := Fin.succ r),
    sigPerm_apply (j := j) (i := i) (r := r)]
  by_cases h1 : (r : ℕ) = i
  · rw [if_pos h1]
    have h1' : ((Fin.succ r : Fin _) : ℕ) = i + 1 := by simp [Fin.val_succ, h1]
    rw [if_pos h1'] <;> rfl
  · rw [if_neg h1]
    by_cases h2 : (r : ℕ) = i + 1
    · rw [if_pos h2]
      have h1' : ¬ (((Fin.succ r : Fin _) : ℕ) = i + 1) := by simp [Fin.val_succ, h2]
      have h2' : ((Fin.succ r : Fin _) : ℕ) = i + 2 := by simp [Fin.val_succ, h2]
      rw [if_neg h1', if_pos h2'] <;> rfl
    · rw [if_neg h2]
      have h1' : ¬ (((Fin.succ r : Fin _) : ℕ) = i + 1) := by
        simp only [Fin.val_succ]; omega
      have h2' : ¬ (((Fin.succ r : Fin _) : ℕ) = i + 2) := by
        simp only [Fin.val_succ]; omega
      rw [if_neg h1', if_neg h2'] <;> rfl

/-- The transposition of the next level fixes the new first slot. -/
theorem sigPerm_zero (j i : ℕ) :
    sigPerm j (i + 1) (0 : Fin ((j + 2 + (i + 1)) + 4)) = 0 := by
  rw [sigPerm_apply]
  rw [if_neg (by simp), if_neg (by simp)]

/-! ## Tuple bookkeeping -/

/-- A tuple is its own head followed by its shifted tail. -/
theorem cons_succ_eta {n : ℕ} (G : Fin (n + 1) → Tf) :
    Fin.cons (G 0) (fun i : Fin n => G i.succ) = G := by
  funext r
  induction r using Fin.cases with
  | zero => rfl
  | succ u => rfl

/-- Prepending the head to the `sigPerm`-shifted tail gives the `sigPerm`-shifted tuple at the next
level. -/
theorem cons_tupSw_sigPerm {j i : ℕ} (G : Fin ((j + 2 + (i + 1)) + 4) → Tf) :
    Fin.cons (G 0)
        (Work.Diff.GE.tupSw (sigPerm j i) (fun r : Fin ((j + 2 + i) + 4) => G r.succ))
      = fun r : Fin ((j + 2 + (i + 1)) + 4) => G (sigPerm j (i + 1) r) := by
  funext r
  induction r using Fin.cases with
  | zero => simp [sigPerm_zero]
  | succ u => simp only [Fin.cons_succ, Work.Diff.GE.tupSw, sigPerm_succ_succ]

/-! ## The induction step -/

/-- **The induction step of the packing identity.**  If the level-`(j+2+i)` tower satisfies the
swap identity with the reindexing `sigPerm j i` and with the difference operator `τ'`, then the
level-`(j+2+i+1)` tower satisfies it with the reindexing `sigPerm j (i+1)` and with the operator
`extStep g τ'`.  This is `Work.Diff.GE.extD_sub_swap` read through `Work.Diff.EXT.extD_ckt`. -/
theorem ladderStep_step_of (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (j i : ℕ)
    (τ' : (Fin ((j + 2 + i) + 4) → Tf) → M → ℝ)
    (hpt : ∀ F : Fin ((j + 2 + i) + 4) → Tf, (∀ u, SmTf (I := I) (M := M) (F u)) →
      ckt g (j + 2 + i) F - ckt g (j + 2 + i) (fun r => F (sigPerm j i r)) = -τ' F) :
    ∀ (G : Fin ((j + 2 + (i + 1)) + 4) → Tf), (∀ u, SmTf (I := I) (M := M) (G u)) →
      ckt g (j + 2 + (i + 1)) G
          - ckt g (j + 2 + (i + 1)) (fun r => G (sigPerm j (i + 1) r))
        = - extStep (I := I) (M := M) g τ' G := by
  intro G hG
  obtain ⟨hcov⟩ := (hLC g).1
  have hF : Work.Diff.GE.SmoothTuple (I := I) (M := M)
      (fun r : Fin ((j + 2 + i) + 4) => G r.succ) := fun r => hG r.succ
  have hG0 : Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G 0) := hG 0
  have hτ : ∀ F : Fin ((j + 2 + i) + 4) → Tf, Work.Diff.GE.SmoothTuple (I := I) (M := M) F →
      Work.Diff.GE.SmoothFunT (I := I) (M := M) (ckt g (j + 2 + i) F) :=
    fun F hF' => (Work.Diff.EXT.tensProp_all hLC g (j + 2 + i) F hF').1
  funext y
  have key := Work.Diff.GE.extD_sub_swap (I := I) (M := M) (sigPerm j i) (sigPerm_invol j i)
    (Submission.Diff.lcOf g) hcov (ckt g (j + 2 + i)) τ' hτ hpt y (G 0) hG0
    (fun r : Fin ((j + 2 + i) + 4) => G r.succ) hF
  rw [Work.Diff.EXT.extD_ckt, Work.Diff.EXT.extD_ckt,
    ← extStep_eq_extD (I := I) (M := M) g τ' G y] at key
  rw [cons_succ_eta, cons_tupSw_sigPerm] at key
  exact key

/-! ## The packing identity -/

/-- **The packing identity, in level form.**  For every `i`, the difference of the level-`(j+2+i)`
tower at a tuple and at its `sigPerm`-reindexing is the `i`-fold `extStep` of the curvature action
`curvActT g j`, up to sign. -/
theorem swapDiff_ladder (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (j : ℕ) :
    ∀ i : ℕ, ∀ (G : Fin ((j + 2 + i) + 4) → Tf),
      (∀ u, SmTf (I := I) (M := M) (G u)) →
      ckt g (j + 2 + i) G - ckt g (j + 2 + i) (fun r => G (sigPerm j i r))
        = - ladderStep (I := I) (M := M) g j i (curvActT (I := I) (M := M) g j) G := by
  intro i
  induction i with
  | zero =>
    intro G hG
    have hsub : (fun r : Fin ((j + 2 + 0) + 4) => G (sigPerm j 0 r))
        = Work.Diff.GE.tupSw (⇑(Work.Diff.EXT.swapFirstTwo (j + 4))) G := by
      funext r
      rw [sigPerm_apply]
      rw [Work.Diff.EXT.tupSw_swapFirstTwo]
      induction r using Fin.cases with
      | zero => rfl
      | succ u =>
        induction u using Fin.cases with
        | zero => rfl
        | succ v => rfl
    rw [hsub, Work.Diff.EXT.ckt_sub_swap hLC g j (fun i => hG i)]
    rfl
  | succ i ih =>
    exact ladderStep_step_of (I := I) (M := M) hLC g j i
      (ladderStep (I := I) (M := M) g j i (curvActT (I := I) (M := M) g j)) ih

/-! ## Relation to `tupSwap` and the final statement -/

/-- `ckt` is invariant under a `Fin.cast` reindexing of its tuple at an equal level. -/
theorem ckt_finCast {d d' : ℕ} (h : d = d') (g : SMet I M) (x : M)
    (F : Fin (d + 4) → Tf) :
    ckt g d F x = ckt g d' (fun r : Fin (d' + 4) => F (Fin.cast (by omega) r)) x := by
  subst h
  congr 1

/-- The index map of `tupSwap` at level `d` with the two adjacent positions `p`, `p + 1`. -/
noncomputable def tupSwapIdx (d p : ℕ) (hp : p + 2 ≤ d) (r : Fin (d + 4)) : Fin (d + 4) :=
  if (r : ℕ) = p then ⟨p + 1, by omega⟩
  else if (r : ℕ) = p + 1 then ⟨p, by omega⟩ else r

/-- `tupSwap` reindexes a tuple by `tupSwapIdx`. -/
theorem tupSwap_eq_idx (d p : ℕ) (hp : p + 2 ≤ d) (G : Fin (d + 4) → Tf) :
    tupSwap (I := I) (M := M) d p hp G = fun r => G (tupSwapIdx d p hp r) := rfl

/-- At the end of the chain of transpositions the reindexing is exactly `tupSwap`. -/
theorem tupSw_sigPerm_val (d p : ℕ) (hp : p + 2 ≤ d)
    (r : Fin (((d - 2 - p) + 2 + p) + 4)) :
    ((Fin.cast (by omega : ((d - 2 - p) + 2 + p) + 4 = d + 4)
        (sigPerm (d - 2 - p) p r) : Fin (d + 4)) : ℕ)
      = ((tupSwapIdx d p hp (Fin.cast (by omega : ((d - 2 - p) + 2 + p) + 4 = d + 4) r)
          : Fin (d + 4)) : ℕ) := by
  rw [sigPerm_apply]
  unfold tupSwapIdx
  simp only [Fin.val_cast]
  split_ifs <;> rfl

/-- At the end of the chain of transpositions the reindexing is exactly `tupSwap`. -/
theorem tupSw_sigPerm_eq (d p : ℕ) (hp : p + 2 ≤ d)
    (r : Fin (((d - 2 - p) + 2 + p) + 4)) :
    Fin.cast (by omega : ((d - 2 - p) + 2 + p) + 4 = d + 4) (sigPerm (d - 2 - p) p r)
      = tupSwapIdx d p hp (Fin.cast (by omega : ((d - 2 - p) + 2 + p) + 4 = d + 4) r) :=
  Fin.ext (tupSw_sigPerm_val d p hp r)

/-- **The packing identity for `tupSwap`.**  The difference of the level-`d` tower at a tuple and at
its `(p, p+1)`-swap is the `p`-fold `extStep` of the curvature action at level `d−2−p`. -/
theorem ckt_sub_tupSwap_eq (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (x : M)
    (d p : ℕ) (hp : p + 2 ≤ d)
    (G : Fin (d + 4) → Tf) (hG : ∀ u, SmTf (I := I) (M := M) (G u)) :
    ckt g d G x - ckt g d (tupSwap (I := I) (M := M) d p hp G) x
      = - ladderStep (I := I) (M := M) g (d - 2 - p) p
          (curvActT (I := I) (M := M) g (d - 2 - p))
          (fun r : Fin (((d - 2 - p) + 2 + p) + 4) => G (Fin.cast (by omega) r)) x := by
  set G' : Fin (((d - 2 - p) + 2 + p) + 4) → Tf :=
    fun r => G (Fin.cast (by omega) r) with hG'
  have hG'sm : ∀ u, SmTf (I := I) (M := M) (G' u) := fun u => hG _
  have hmain := congrFun (swapDiff_ladder (I := I) (M := M) hLC g (d - 2 - p) p G' hG'sm) x
  simp only [Pi.sub_apply, Pi.neg_apply] at hmain
  have htail : (fun r : Fin (((d - 2 - p) + 2 + p) + 4) => G' (sigPerm (d - 2 - p) p r))
      = fun r : Fin (((d - 2 - p) + 2 + p) + 4) =>
          tupSwap (I := I) (M := M) d p hp G (Fin.cast (by omega) r) := by
    funext r
    simp only [hG']
    rw [tupSwap_eq_idx, tupSw_sigPerm_eq d p hp r]
  have hhead : ckt g ((d - 2 - p) + 2 + p) G' x = ckt g d G x := by
    rw [ckt_finCast (by omega : d = (d - 2 - p) + 2 + p) g x G]
  have htail2 : ckt g ((d - 2 - p) + 2 + p)
      (fun r : Fin (((d - 2 - p) + 2 + p) + 4) =>
        tupSwap (I := I) (M := M) d p hp G (Fin.cast (by omega) r)) x
      = ckt g d (tupSwap (I := I) (M := M) d p hp G) x := by
    rw [ckt_finCast (by omega : d = (d - 2 - p) + 2 + p) g x
      (tupSwap (I := I) (M := M) d p hp G)]
  rw [htail, htail2, hhead] at hmain
  exact hmain

end Work.Diff.EXT.evolX
