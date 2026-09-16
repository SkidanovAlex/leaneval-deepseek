import Submission.ZagierHoffmanProof.StepK29

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K30: the `D1 ↔ D2` glue (stage-1 data specialisation of `St_step`)

  St_stage1_is_D1 (m) (u) : St F (m+2) 1 (cons 0 (cons 0 u)) = D1 F (m+1)(cons 0 u)
      [rw [D1_def' F m (cons 0 u)] + dsimp [St] — closes by dsimp alone]
  St_stage1_head (m) (u) : coeffSeq F (m+2) (cons 0 (cons 0 u)) 1 = 0
      [coeffSeq_lt at 1 (⟨0,·⟩.succ = ⟨1,·⟩), Fin.cons_succ with explicit α; then
      rewrite the zero element ⟨0,·⟩ to `0` (Fin.ext) BEFORE Fin.cons_zero — rw
      [Fin.cons_zero] on ⟨0,·⟩ FAILS]
  St_stage1_D2 (m) (u) : (Σ_{m'< (m+2)−1} coeffSeq(m+2)(cons0(cons0 u))(m'+1+1)·hh 0 3 m')
      = D2 F m u   [dsimp [D2] — closed]
  ★ D1_D2_glue (m) (u) : D1 (m+1)(cons 0 u) − (D1 (m+1)(cons 0 u))^q
      = (X − X^{(q)^2})·D2 m u
      [St_step at (m+2, 1, cons 0 (cons 0 u)) + the three identifications + C 0 = 0]
All sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]




/-- identification: the stage-1 `St` polynomial at the stage-1 data is `D1 (m+1)(cons 0 u)`. -/
lemma St_stage1_is_D1 (m : ℕ) (u : Fin m → F) :
    St F (m + 2) 1 (Fin.cons 0 (Fin.cons 0 u)) = D1 F (m + 1) (Fin.cons 0 u) := by
  classical
  rw [D1_def' F m (Fin.cons 0 u)]
  dsimp [St]

/-- the head coefficient at stage-1 data vanishes: `coeffSeq (m+2)(cons0(cons0 u)) 1 = 0`. -/
lemma St_stage1_head (m : ℕ) (u : Fin m → F) :
    coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons 0 u)) 1 = 0 := by
  classical
  have hlt : 1 < m + 2 := by omega
  rw [coeffSeq_lt F (m + 2) (Fin.cons 0 (Fin.cons 0 u)) 1 hlt]
  have hs : (⟨0, by omega⟩ : Fin (m + 1)).succ = ⟨1, hlt⟩ := by
    apply Fin.ext
    rfl
  rw [← hs]
  rw [Fin.cons_succ (α := fun _ : Fin (m + 2) => F) (x := (0 : F)) (p := Fin.cons 0 u) ⟨0, by omega⟩]
  have hz : (⟨0, by omega⟩ : Fin (m + 1)) = 0 := by
    apply Fin.ext
    rfl
  rw [hz]
  exact Fin.cons_zero (α := fun _ : Fin (m + 1) => F) (x := (0 : F)) (p := u)

/-- identification: `St_step`'s stage-1 output sum is `D2 m u`. -/
lemma St_stage1_D2 (m : ℕ) (u : Fin m → F) :
    (∑ m' ∈ Finset.range ((m + 2) - 1), C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons 0 u)) (m' + 1 + 1)) * hh F 0 (1 + 2) m') =
      D2 F m u := by
  classical
  dsimp [D2]

/-- ★ THE `D1 ↔ D2` GLUE (stage-1): with `Z(u) := D1 (m+1)(cons 0 u)`,
`Z(u) − Z(u)^q = (X − X^{q²})·D2 m u`. -/
lemma D1_D2_glue (m : ℕ) (u : Fin m → F) :
    D1 F (m + 1) (Fin.cons 0 u) - (D1 F (m + 1) (Fin.cons 0 u)) ^ (Nat.card F) =
      (X - X ^ ((Nat.card F) ^ 2)) * D2 F m u := by
  classical
  have hs := St_step F (m + 2) 1 (Fin.cons 0 (Fin.cons 0 u)) (by omega)
  have hSt := St_stage1_is_D1 F m u
  have hhead := St_stage1_head F m u
  have hD := St_stage1_D2 F m u
  rw [hSt] at hs
  rw [hhead] at hs
  rw [hD] at hs
  -- clean up C 0 and the exponent (Nat.card F)^(1+1) = (Nat.card F)^2
  have hC0 : C (0 : F) = 0 := by simp
  rw [hC0] at hs
  simpa using hs

end ZagierHoffmanPositiveChar
