import Submission.ZagierHoffmanProof.StepK25

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K26: the s=1 head-affineness (`D1_cons_add_zero`)

The stage-1 analogue of `monicPd_cons_add_zero` (StepK20): the `D1` denominator is
affine in the next coefficient to collapse, with coefficient `1` —

    D1 (m+1)(Fin.cons c u) = C c + D1 (m+1)(Fin.cons 0 u).

Ingredients (the `monicPd_cons` route, with explicit `Fin` subscripts):
  D1_def' : D1 F (m+1) t unfolds to the `Σ_{m'<m+2} coeffSeq(m+2)(cons 0 t)(m'+1)·hh 0 2 m'`
      sum (the definition-level `(m+1)+1` normalises by `dsimp` to `m+2`);
  D1_coef_head : the index-1 coefficient of `cons 0 (cons x u)` is `x`
      (`⟨0⟩.succ = ⟨1⟩`, `Fin.cons_succ`, `Fin.cons_zero`, explicit dependent-α);
  D1_coef_tail_indep : the index-≥2 coefficients are head-independent
      (`⟨k+2⟩ = succ(succ⟨k⟩)`, two `Fin.cons_succ` reductions to `u⟨k⟩`; the ≥ level
      branch gives `1` via the `coeffSeq` extension).
  D1_cons_add_zero : split the head term (Finset.sum_range_succ') and use the two
      coefficient lemmas + `C 0 = 0` folding.
This is the s=1 instance's affineness step; with `sum_cons_split` + `Hsum_one_subst` at
the c-independent part + `St_step` at stage-1 data it yields the stage-1 collapse
(the `s=1` instance of the general statement in StepK25).  All lemmas are sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]




/-- `D1`'s head coefficient at index 1 (value of the tuple at index 0 of the inner cons). -/
lemma D1_coef_head (m : ℕ) (x : F) (u : Fin m → F) :
    coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons x u)) 1 = x := by
  classical
  have hlt : 1 < m + 2 := by omega
  rw [coeffSeq_lt F (m + 2) (Fin.cons 0 (Fin.cons x u)) 1 hlt]
  have hs : (⟨0, by omega⟩ : Fin (m + 1)).succ = ⟨1, hlt⟩ := by
    apply Fin.ext
    rfl
  rw [← hs]
  rw [Fin.cons_succ (α := fun _ : Fin (m + 2) => F) (x := (0 : F)) (p := Fin.cons x u) ⟨0, by omega⟩]
  have hz : (⟨0, by omega⟩ : Fin (m + 1)) = 0 := by
    apply Fin.ext
    rfl
  rw [hz]
  exact Fin.cons_zero (α := fun _ : Fin (m + 1) => F) (x := x) (p := u)

/-- `D1`'s tail coefficients (indices ≥ 2) are independent of the head value. -/
lemma D1_coef_tail_indep (m : ℕ) (u : Fin m → F) (x x' : F) (k : ℕ) :
    coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons x u)) (k + 2) =
      coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons x' u)) (k + 2) := by
  classical
  by_cases hk : k + 2 < m + 2
  · have h1 := coeffSeq_lt F (m + 2) (Fin.cons 0 (Fin.cons x u)) (k + 2) hk
    have h2 := coeffSeq_lt F (m + 2) (Fin.cons 0 (Fin.cons x' u)) (k + 2) hk
    rw [h1, h2]
    have hred (x0 : F) : (Fin.cons (0 : F) ((Fin.cons x0 u) : Fin (m + 1) → F) : Fin (m + 2) → F) ⟨k + 2, hk⟩ = u ⟨k, by omega⟩ := by
      have hs2 : (⟨k + 1, by omega⟩ : Fin (m + 1)).succ = ⟨k + 2, hk⟩ := by
        apply Fin.ext
        rfl
      have hs1 : (⟨k, by omega⟩ : Fin m).succ = ⟨k + 1, by omega⟩ := by
        apply Fin.ext
        rfl
      rw [← hs2]
      rw [Fin.cons_succ (α := fun _ : Fin (m + 2) => F) (x := (0 : F)) (p := Fin.cons x0 u) ⟨k + 1, by omega⟩]
      rw [← hs1]
      rw [Fin.cons_succ (α := fun _ : Fin (m + 1) => F) (x := x0) (p := u) ⟨k, by omega⟩]
    rw [hred x, hred x']
  · have hbig : ¬ k + 2 < m + 2 := by omega
    dsimp [coeffSeq]
    simp [hbig]

/-- `D1 F (m+1) t` with its definition-level normalised from `(m+1)+1` to `m+2`
(the two are equal but NOT defeq — `rw [D1_def']` confines the level noise to one step). -/
lemma D1_def' (m : ℕ) (t : Fin (m + 1) → F) :
    D1 F (m + 1) t = ∑ m' ∈ Finset.range (m + 2), C (coeffSeq F (m + 2) (Fin.cons 0 t) (m' + 1)) * hh F 0 2 m' := by
  classical
  dsimp [D1]

/-- the affine structure of `D1` in the head coefficient (stage-1 analogue of
`monicPd_cons_add_zero`): `D1 (m+1)(cons c u) = C c + D1 (m+1)(cons 0 u)`. -/
lemma D1_cons_add_zero (m : ℕ) (c : F) (u : Fin m → F) :
    D1 F (m + 1) (Fin.cons c u) = C c + D1 F (m + 1) (Fin.cons 0 u) := by
  classical
  have hsplit (x : F) :
      (∑ m' ∈ Finset.range (m + 2), C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons x u)) (m' + 1)) * hh F 0 2 m')
        = (∑ k ∈ Finset.range (m + 1), C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons x u)) (k + 2)) * hh F 0 2 (k + 1)) + C x := by
    rw [Finset.sum_range_succ']
    have h0 : C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons x u)) (0 + 1)) * hh F 0 2 0 = C x := by
      have hh0 : hh F 0 2 0 = 1 := hh_zero F 0 2
      rw [hh0]
      have hx := D1_coef_head F m x u
      simpa using congrArg (fun t : F => C t) hx
    rw [h0]
  calc
    D1 F (m + 1) (Fin.cons c u)
        = (∑ k ∈ Finset.range (m + 1), C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons c u)) (k + 2)) * hh F 0 2 (k + 1)) + C c := by
          rw [D1_def' F m (Fin.cons c u)]
          exact hsplit c
    _ = C c + (∑ k ∈ Finset.range (m + 1), C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons 0 u)) (k + 2)) * hh F 0 2 (k + 1)) := by
          rw [show (∑ k ∈ Finset.range (m + 1), C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons c u)) (k + 2)) * hh F 0 2 (k + 1)) = (∑ k ∈ Finset.range (m + 1), C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons 0 u)) (k + 2)) * hh F 0 2 (k + 1)) by
            apply Finset.sum_congr rfl
            intro k hk
            rw [D1_coef_tail_indep F m u c 0 k]]
          ring
    _ = C c + D1 F (m + 1) (Fin.cons 0 u) := by
          rw [D1_def' F m (Fin.cons 0 u)]
          have hs0 := hsplit (0 : F)
          have hz0 : C (0 : F) = 0 := by simp
          have hfold : (∑ k ∈ Finset.range (m + 1), C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons 0 u)) (k + 2)) * hh F 0 2 (k + 1)) =
              (∑ m' ∈ Finset.range (m + 2), C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons 0 u)) (m' + 1)) * hh F 0 2 m') := by
            rw [hs0]
            rw [hz0]
            simp
          rw [hfold]


end ZagierHoffmanPositiveChar
