import Submission.ZagierHoffmanProof.StepK22

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K23: the s=0 stage specialisation, connected to the glue

  ★ St_zero_glue (d) (a) : `St_0(a) = monicPd d a` — at stage 0 the collapse
    denominator is the monic polynomial itself (`hh 0 1 m = X^m`, sum_range_succ split
    of the leading `X^d`, `Finset.sum_fin_eq_sum_range` for the Fin-sum).
  ★ St_step_zero (n) (t) : with `a := Fin.cons 0 t` the uniform `St_step` at s = 0
    specialises to the StepK21 `stage0_factor`: `Z₀ − Z₀^q = (X − X^q)·D₁(t)` where
    `Z₀ = monicPd (n+1)(cons 0 t)` and `D₁(t) := Σ_{m<n+1} coeffSeq(m+1)·hh 0 2 m`
    (St_zero_glue identifies `St_0` with `Z₀`, and the removed head coefficient is `0`).

This is the first block of the E-assembly: with the `a₀`-collapse (StepK20
`Hsum_collapse0_inner`) and the `finSuccSplit` coordinate reindexing it yields
`Hsum F (n+1) 1 = (X−X^q)⁻¹·Σ_{t : Fin n → F} inv(cast(D₁(t)))`.  All lemmas here are
sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]




/-- at stage 0 the collapse denominator is the monic polynomial itself:
`St_0(a) = monicPd d a`. -/
lemma St_zero_glue (d : ℕ) (a : Fin d → F) : St F d 0 a = monicPd F d a := by
  classical
  have hhh (m : ℕ) : hh F 0 1 m = X ^ m := by
    rw [hh_one F 0 m]
    simp
  have hmain : (∑ m ∈ Finset.range d, C (coeffSeq F d a m) * X ^ m) = ∑ j : Fin d, C (a j) * X ^ (j.1) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro m hm
    have hm' : m < d := Finset.mem_range.mp hm
    rw [dif_pos hm']
    rw [coeffSeq_lt F d a m hm']
  calc
    St F d 0 a = ∑ m ∈ Finset.range (d + 1), C (coeffSeq F d a m) * X ^ m := by
          dsimp [St]
          have hhrew : (∑ m ∈ Finset.range (d + 1), C (coeffSeq F d a m) * hh F 0 1 m) =
              ∑ m ∈ Finset.range (d + 1), C (coeffSeq F d a m) * X ^ m := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [hhh m]
          rw [hhrew]
    _ = (∑ m ∈ Finset.range d, C (coeffSeq F d a m) * X ^ m) + X ^ d := by
          rw [Finset.sum_range_succ]
          have hd : coeffSeq F d a d = 1 := coeffSeq_d F d a
          rw [hd]
          have hC1 : C (1 : F) = 1 := by simp
          rw [hC1]
          simp
    _ = monicPd F d a := by
          rw [hmain]
          dsimp [monicPd]
          ring


/-- the s=0 specialisation of `St_step`, connected to the `Z₀`-glue: with
`a := cons 0 t`, `St_0 = Z₀ = monicPd (n+1)(cons 0 t)` and the head term is `0`, so
`Z₀ − Z₀^q = (X − X^q)·D₁(t)` (the StepK21 `stage0_factor` content, rederived from the
uniform `St_step`). -/
lemma St_step_zero (n : ℕ) (t : Fin n → F) :
    monicPd F (n + 1) (Fin.cons 0 t) - (monicPd F (n + 1) (Fin.cons 0 t)) ^ (Nat.card F) =
      (X - X ^ (Nat.card F)) *
        (∑ m ∈ Finset.range (n + 1), C (coeffSeq F (n + 1) (Fin.cons 0 t) (m + 1)) * hh F 0 2 m) := by
  classical
  have hs := St_step F (n + 1) 0 (Fin.cons 0 t) (by omega)
  have hz := St_zero_glue F (n + 1) (Fin.cons 0 t)
  have hc0 : coeffSeq F (n + 1) (Fin.cons 0 t) 0 = 0 := by
    have hlt : 0 < n + 1 := by omega
    rw [coeffSeq_lt F (n + 1) (Fin.cons 0 t) 0 hlt]
    exact Fin.cons_zero (α := fun _ : Fin (n + 1) => F) (x := (0 : F)) (p := t)
  rw [hz] at hs
  rw [hc0] at hs
  simpa using hs



end ZagierHoffmanPositiveChar
