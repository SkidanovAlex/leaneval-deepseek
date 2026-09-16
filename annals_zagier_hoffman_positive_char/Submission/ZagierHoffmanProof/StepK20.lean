import Submission.ZagierHoffmanProof.StepK19
import Submission.ZagierHoffmanProof.StepK14

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K20: the coordinate split and the `a₀`-collapse of the tuple `Hsum`

The first nested stage of the `EvalStep d` collapse (PLAN SESSION 153).  Coefficients
are `Fin (n+1)`-tuples with index `0` = the constant coefficient `a₀`.  The coordinate
split is `finSuccSplit : (Fin (n+1) → F) ≃ F × (Fin n → F)`, splitting off `a₀` with
tail `t` (the values on `succ`s), inverse `Fin.cons`.  Under the split the monic
polynomial is `monicPd (n+1)(cons c t) = C c + Z₀(t)` (`monicPd_cons`,
`monicPd_cons_add_zero`) with the `c`-independent part
`Z₀(t) = monicPd (n+1)(cons 0 t) = X^{n+1} + Σ C(t k)·X^{k+1}`; the constant-coefficient
sum is the `Hsum_one_subst` collapse `Σ_c inv(C c + Z₀) = inv(Z₀ − Z₀^q)`
(`Hsum_collapse0_inner`).  The stage factorisation `Z₀ − Z₀^q = (X−X^q)·D₁(t)` is
`stage_step F (n+1) 0 (cons 0 t)` once the `E₀`-sum is identified with `Z₀` (range
`n+1`-sum vs `Fin n`-sum bridge — next session's remaining glue), yielding
`Hsum F (n+1) 1 = (X−X^q)⁻¹·Σ_t inv(D₁(t))`.  All lemmas here are sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]




/-- split a function on `Fin (n+1)` into its value at `0` and the values on the
successors: `(Fin (n+1) → F) ≃ F × (Fin n → F)`. -/
noncomputable def finSuccSplit (n : ℕ) : (Fin (n + 1) → F) ≃ (F × (Fin n → F)) where
  toFun := fun a => (a 0, fun j => a j.succ)
  invFun := fun ct => Fin.cons ct.1 ct.2
  left_inv := by
    intro a
    funext i
    by_cases hi : (i : ℕ) = 0
    · have hi0 : i = 0 := Fin.ext (by simpa using hi)
      rw [hi0]
      exact Fin.cons_zero (α := fun _ : Fin (n + 1) => F) (x := a 0) (p := fun k : Fin n => a k.succ)
    · -- i ≠ 0: i = j.succ for j := ⟨i.1 − 1, _⟩
      let j : Fin n := ⟨i.1 - 1, by
        have hi' : 0 < i.1 := Nat.pos_of_ne_zero hi
        have hi2 : i.1 < n + 1 := i.2
        omega⟩
      have hisucc : i = j.succ := by
        apply Fin.ext
        dsimp [j]
        omega
      rw [hisucc]
      exact Fin.cons_succ (α := fun _ : Fin (n + 1) => F) (x := a 0) (p := fun k : Fin n => a k.succ) j
  right_inv := by
    intro ct
    apply Prod.ext
    · -- first component: (invFun ct) 0 = ct.1
      simp [Fin.cons_zero]
    · funext j
      -- (invFun ct) j.succ = ct.2 j
      exact Fin.cons_succ (α := fun _ : Fin (n + 1) => F) (x := ct.1) (p := ct.2) j




/-- `monicPd (n+1)` with the first coefficient `c` and tail `t`: the polynomial is
`C c + X^{n+1} + Σ_{k<n} C(t k)·X^{k+1}` (the `c`-term is the constant). -/
lemma monicPd_cons (n : ℕ) (c : F) (t : Fin n → F) :
    monicPd F (n + 1) (Fin.cons c t) = C c + X ^ (n + 1) + ∑ k : Fin n, C (t k) * X ^ (k.1 + 1) := by
  classical
  dsimp [monicPd]
  rw [Fin.sum_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]
  ring

/-- the `c`-independent part: `Z₀(t) := monicPd (n+1) (cons 0 t) = X^{n+1}+Σ C(t k)X^{k+1}`. -/
lemma monicPd_zero_cons (n : ℕ) (t : Fin n → F) :
    monicPd F (n + 1) (Fin.cons 0 t) = X ^ (n + 1) + ∑ k : Fin n, C (t k) * X ^ (k.1 + 1) := by
  rw [monicPd_cons F n 0 t]
  have hC0 : C (0 : F) = 0 := by simp
  rw [hC0]
  simp

/-- `Z₀` is nonconstant (needed for the `Hsum_one_subst` instance). -/
lemma monicPd_zero_cons_nonconst (n : ℕ) (t : Fin n → F) :
    (monicPd F (n + 1) (Fin.cons 0 t)).natDegree ≠ 0 := by
  rw [monicPd_natDegree F (n + 1) (Fin.cons 0 t)]
  omega

/-- splitting `monicPd (n+1)(cons c t) = C c + Z₀(t)`. -/
lemma monicPd_cons_add_zero (n : ℕ) (c : F) (t : Fin n → F) :
    monicPd F (n + 1) (Fin.cons c t) = C c + monicPd F (n + 1) (Fin.cons 0 t) := by
  rw [monicPd_cons F n c t]
  rw [monicPd_zero_cons F n t]
  ring

/-- ★ the constant-coefficient collapse (`a₀`-sum as `Hsum_one_subst` at `Z₀(t)`):
`Σ_c inv(C c + Z₀) = inv(Z₀ − Z₀^q)`. -/
lemma Hsum_collapse0_inner (n : ℕ) (t : Fin n → F) :
    letI : Fintype F := Fintype.ofFinite F
    (∑ c : F, ((((C c + monicPd F (n + 1) (Fin.cons 0 t) : F[X]) : F[X]) : RatFunc F)⁻¹)) =
      ((((monicPd F (n + 1) (Fin.cons 0 t) - (monicPd F (n + 1) (Fin.cons 0 t)) ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have h := Hsum_one_subst F (monicPd F (n + 1) (Fin.cons 0 t)) (monicPd_zero_cons_nonconst F n t)
  -- h : Σ_c (Z₀ + C c)⁻¹ = (Z₀ − Z₀^q)⁻¹
  simpa [add_comm] using h

end ZagierHoffmanPositiveChar
