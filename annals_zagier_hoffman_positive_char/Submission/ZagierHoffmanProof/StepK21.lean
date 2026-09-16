import Submission.ZagierHoffmanProof.StepK20

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K21: the `E₀ = Z₀` glue and the s=0 stage factorisation

The bridge between the general tuple sum `Hsum F (n+1) 1 = Σ_a inv(monicPd (n+1) a)`
(StepK19) and the collapsed form built in StepK20:
  ★ stageE0_eq_Z0 : the `stage_step` `E₀`-sum (over `Finset.range (n+1)` with
    `coeffSeq (cons 0 t)`) equals `Z₀(t) = monicPd (n+1)(cons 0 t)` — via
    `Finset.sum_range_succ` (split off the leading `X^{n+1}` term), `hh 0 1 (m+1) =
    X^{m+1}` (`hh_one`), per-`m` `coeffSeq (cons 0 t)(m+1) = t⟨m⟩` (`coeffSeq_lt` +
    `Fin.cons_succ`), and `Finset.sum_fin_eq_sum_range` (with `dif_pos`, NOT `if_pos`,
    for the guarded `⟨m,·⟩`);
  ★ stage0_factor : `Z₀(t) − Z₀(t)^q = (X − X^q)·D₁(t)`, `D₁(t) :=
    Σ_{m<n+1} coeffSeq(m+1)·hh 0 2 m` — `stage_step F (n+1) 0 (cons 0 t)` cleaned by
    `simpa` (index arithmetic `(n+1)−0`, `m+0+1`, `0+1`, `0+2`), then `rw [stageE0_eq_Z0]`.
This is the s=0 output shape that iterates for s = 1..n−1 on the shrinking tuple spaces
(the `hh`-variable count grows by one per stage); with the `a₀`-collapse of StepK20 it
yields `Hsum F (n+1) 1 = (X−X^q)⁻¹·Σ_{t:Fin n→F} inv(cast(D₁ t))`.  All lemmas here are
sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]




/-- ★ GLUE: the `stage_step` `E₀`-sum (over `range (n+1)` with `coeffSeq (cons 0 t)`)
equals `Z₀(t) = monicPd (n+1)(cons 0 t)`. -/
lemma stageE0_eq_Z0 (n : ℕ) (t : Fin n → F) :
    (∑ m ∈ Finset.range (n + 1), C (coeffSeq F (n + 1) (Fin.cons 0 t) (m + 1)) * hh F 0 1 (m + 1)) =
      monicPd F (n + 1) (Fin.cons 0 t) := by
  classical
  have hhh (m : ℕ) : hh F 0 1 (m + 1) = X ^ (m + 1) := by
    rw [hh_one F 0 (m + 1)]
    simp
  have hmain : (∑ m ∈ Finset.range n, C (coeffSeq F (n + 1) (Fin.cons 0 t) (m + 1)) * X ^ (m + 1)) =
      ∑ k : Fin n, C (t k) * X ^ (k.1 + 1) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro m hm
    have hm' : m < n := Finset.mem_range.mp hm
    rw [dif_pos hm']
    have hlt : m + 1 < n + 1 := by omega
    have hcs : coeffSeq F (n + 1) (Fin.cons 0 t) (m + 1) = t ⟨m, hm'⟩ := by
      rw [coeffSeq_lt F (n + 1) (Fin.cons 0 t) (m + 1) hlt]
      have hs : (⟨m, hm'⟩ : Fin n).succ = ⟨m + 1, hlt⟩ := by
        apply Fin.ext
        rfl
      rw [← hs]
      exact Fin.cons_succ (α := fun _ : Fin (n + 1) => F) (x := (0 : F)) (p := t) ⟨m, hm'⟩
    rw [hcs]
  calc
    (∑ m ∈ Finset.range (n + 1), C (coeffSeq F (n + 1) (Fin.cons 0 t) (m + 1)) * hh F 0 1 (m + 1))
        = (∑ m ∈ Finset.range n, C (coeffSeq F (n + 1) (Fin.cons 0 t) (m + 1)) * hh F 0 1 (m + 1))
            + C (coeffSeq F (n + 1) (Fin.cons 0 t) (n + 1)) * hh F 0 1 (n + 1) := by
          rw [Finset.sum_range_succ]
    _ = (∑ m ∈ Finset.range n, C (coeffSeq F (n + 1) (Fin.cons 0 t) (m + 1)) * X ^ (m + 1))
            + C (coeffSeq F (n + 1) (Fin.cons 0 t) (n + 1)) * X ^ (n + 1) := by
          congr 1
          · apply Finset.sum_congr rfl
            intro m hm
            rw [hhh m]
          · rw [hhh n]
    _ = (∑ m ∈ Finset.range n, C (coeffSeq F (n + 1) (Fin.cons 0 t) (m + 1)) * X ^ (m + 1))
            + X ^ (n + 1) := by
          have hd : coeffSeq F (n + 1) (Fin.cons 0 t) (n + 1) = 1 := coeffSeq_d F (n + 1) (Fin.cons 0 t)
          rw [hd]
          simp
    _ = (∑ k : Fin n, C (t k) * X ^ (k.1 + 1)) + X ^ (n + 1) := by
          rw [hmain]
    _ = monicPd F (n + 1) (Fin.cons 0 t) := by
          rw [monicPd_zero_cons F n t]
          ring

/-- ★ the s=0 stage factorisation in `Z₀`/`D₁` form:
`Z₀(t) − Z₀(t)^q = (X − X^q)·D₁(t)`, `D₁(t) := Σ_{m<n+1} coeffSeq(m+1)·hh 0 2 m`. -/
lemma stage0_factor (n : ℕ) (t : Fin n → F) :
    monicPd F (n + 1) (Fin.cons 0 t) - (monicPd F (n + 1) (Fin.cons 0 t)) ^ (Nat.card F) =
      (X - X ^ (Nat.card F)) *
        (∑ m ∈ Finset.range (n + 1), C (coeffSeq F (n + 1) (Fin.cons 0 t) (m + 1)) * hh F 0 2 m) := by
  classical
  have hs := stage_step F (n + 1) 0 (Fin.cons 0 t)
  have hs0 : (∑ m ∈ Finset.range (n + 1), C (coeffSeq F (n + 1) (Fin.cons 0 t) (m + 1)) * hh F 0 1 (m + 1))
      - ((∑ m ∈ Finset.range (n + 1), C (coeffSeq F (n + 1) (Fin.cons 0 t) (m + 1)) * hh F 0 1 (m + 1)) ^ (Nat.card F)) =
      (X - X ^ (Nat.card F)) *
        (∑ m ∈ Finset.range (n + 1), C (coeffSeq F (n + 1) (Fin.cons 0 t) (m + 1)) * hh F 0 2 m) := by
    simpa using hs
  rw [stageE0_eq_Z0 F n t] at hs0
  simpa using hs0


end ZagierHoffmanPositiveChar
