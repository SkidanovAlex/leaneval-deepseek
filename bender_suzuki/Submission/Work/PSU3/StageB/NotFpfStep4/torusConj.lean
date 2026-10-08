import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.Model.psu3_datum
import Submission.Work.PSU3.Model.psu3_uEquiv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.NotFpfStep4

open Matrix LeanEval.GroupTheory.Defs

/-- **Torus conjugation on the matrix model.**  For `a ∈ GF(q²)ˣ` with `a^(q+1) = 1`
(`q = 2ⁿ`), conjugating the unipotent `A(x,y) = u(x,y)` by the inverse of the torus element
`t(a) = diag(a, a^(q-1), a^(-q))` produces `A(a⁻³ x, a⁻³ σ(a⁻³) y)`, i.e. the matrix of
`SZ.torusAct (a⁻¹)³ p`.  The two exponents `a⁻¹·a^(q-1) = a⁻³` and `a⁻³·σ(a⁻³) = 1`
use exactly the relation `a^(q+1) = 1`. -/
lemma matGL_conj_suTg {n : ℕ} (a : (Submission.PSU3.F n)ˣ)
    (ha : (a : Submission.PSU3.F n) ^ (2 ^ n + 1) = 1)
    (p : Work.PSU3.SZ (Work.PSU3.E n)) :
    (Submission.PSU3.suTg n a)⁻¹ * Work.PSU3.matGL p * Submission.PSU3.suTg n a =
      Work.PSU3.matGL (Work.PSU3.SZ.torusAct (a⁻¹ ^ 3) p) := by
  have haU : a ^ (2 ^ n + 1) = 1 := Units.ext (by simpa using ha)
  have hq : a ^ (2 ^ n) = a⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ, haU])
  have hqv : ((a : Submission.PSU3.F n)) ^ (2 ^ n) = ((a : Submission.PSU3.F n))⁻¹ := by
    have := congrArg Units.val hq
    simpa [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val] using this
  have hsing : (↑(a⁻¹ ^ 3) : Submission.PSU3.F n) = ((a : Submission.PSU3.F n))⁻¹ ^ 3 := by
    simp [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  -- `a⁻¹ * a^(q-1) = (a⁻¹)³`
  have hc : ((a : Submission.PSU3.F n))⁻¹ * ((a : Submission.PSU3.F n)) ^ (2 ^ n - 1)
      = (↑(a⁻¹ ^ 3) : Submission.PSU3.F n) := by
    have hm : 2 ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have hp : a ^ (2 ^ n - 1) = a ^ (2 ^ n) * a⁻¹ :=
      eq_mul_inv_of_mul_eq (pow_sub_one_mul hm a)
    have key : a⁻¹ * a ^ (2 ^ n - 1) = a⁻¹ ^ 3 := by rw [hp, hq]; group
    simpa using congrArg Units.val key
  -- `a⁻¹ * (a^q)⁻¹ = 1`
  have hc2 : ((a : Submission.PSU3.F n))⁻¹ * (((a : Submission.PSU3.F n)) ^ (2 ^ n))⁻¹ = 1 := by
    have key : a⁻¹ * (a ^ (2 ^ n))⁻¹ = 1 := by rw [hq, inv_inv, inv_mul_cancel]
    simpa using congrArg Units.val key
  -- `(a⁻¹)³ * σ((a⁻¹)³) = 1`
  have hc2' : (↑(a⁻¹ ^ 3) : Submission.PSU3.F n) *
      Work.PSU3.σE (↑(a⁻¹ ^ 3) : Submission.PSU3.F n) = 1 := by
    have hsigma : Work.PSU3.σE (((a : Submission.PSU3.F n))⁻¹ ^ 3)
        = ((a : Submission.PSU3.F n)) ^ 3 := by
      rw [map_pow, Work.PSU3.σE_inv, Work.PSU3.Model.sigmaE_eq_pow, hqv, inv_inv]
    rw [hsing, hsigma, inv_pow]
    exact inv_mul_cancel₀ (pow_ne_zero 3 (Units.ne_zero a))
  have hA1 : ((a : Submission.PSU3.F n))⁻¹ * p.x * ((a : Submission.PSU3.F n)) ^ (2 ^ n - 1)
      = (↑(a⁻¹ ^ 3) : Submission.PSU3.F n) * p.x := by
    rw [mul_right_comm, hc]
  have hA2 : ((a : Submission.PSU3.F n))⁻¹ * p.y * (((a : Submission.PSU3.F n)) ^ (2 ^ n))⁻¹
      = (↑(a⁻¹ ^ 3) : Submission.PSU3.F n) *
          Work.PSU3.σE (↑(a⁻¹ ^ 3) : Submission.PSU3.F n) * p.y := by
    rw [mul_right_comm, hc2, hc2', one_mul]
  have hmat : Work.PSU3.matGL p = Submission.PSU3.suUg n p.x p.y :=
    Work.PSU3.Model.matGL_mk_eq_suUg n p.x p.y p.herm
  have hmat' : Work.PSU3.matGL (Work.PSU3.SZ.torusAct (a⁻¹ ^ 3) p)
      = Submission.PSU3.suUg n (Work.PSU3.SZ.torusAct (a⁻¹ ^ 3) p).x
          (Work.PSU3.SZ.torusAct (a⁻¹ ^ 3) p).y :=
    Work.PSU3.Model.matGL_mk_eq_suUg n _ _ _
  rw [hmat, hmat', Submission.PSU3.suTg_conj_suUg' n a p.x p.y,
      Work.PSU3.SZ.torusAct_x, Work.PSU3.SZ.torusAct_y, hA1, hA2]

lemma torusConj {n : ℕ} (hn : 2 ≤ n) (a : (Submission.PSU3.F n)ˣ)
    (ha : (a : Submission.PSU3.F n) ^ (2 ^ n + 1) = 1)
    (p : Work.PSU3.SZ (Work.PSU3.E n)) :
    (Submission.PSU3.psu3Hom n (Submission.PSU3.suTgSU n a))⁻¹ *
        (⟨Work.PSU3.pglHom p, Work.PSU3.Model.pglHom_mem_PSU3Model n p⟩ :
          LeanEval.GroupTheory.Defs.PSU3Model n) *
        Submission.PSU3.psu3Hom n (Submission.PSU3.suTgSU n a) =
      (⟨Work.PSU3.pglHom (Work.PSU3.SZ.torusAct (a⁻¹ ^ 3) p),
          Work.PSU3.Model.pglHom_mem_PSU3Model n _⟩ :
        LeanEval.GroupTheory.Defs.PSU3Model n) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv,
    Submission.PSU3.psu3Hom_apply, Submission.PSU3.suTgSU_val, Work.PSU3.pglHom_apply]
  rw [← map_inv, ← map_mul, ← map_mul]
  rw [matGL_conj_suTg a ha p]

end Work.PSU3.StageB.NotFpfStep4
