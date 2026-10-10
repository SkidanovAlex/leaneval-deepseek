import Mathlib
import Submission.Work.MotV.PthPowDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

theorem genY_mem_subfield_of_two_eq_zero {N : Type*} [Field N] [IsAlgClosed N]
    (E : WeierstrassCurve N) (p : ℕ) [Fact p.Prime] [CharP N p] (h2 : (2 : N) = 0)
    (he : algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
      algebraMap N (Work.MotC2.Func E) E.a₃ ≠ 0)
    (S : Subfield (Work.MotC2.Func E))
    (hKp : ∀ z ∈ Work.MotV.PthPow (Work.MotC2.Func E) p, z ∈ S)
    (hx : Work.MotC2.genX E ∈ S) : Work.MotC2.genY E ∈ S := by
  have hp2 : p = 2 := by
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff N p 2).mp h2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h (Fact.out : Nat.Prime p).ne_one
    · exact h
  set B : Work.MotC2.Func E := algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
      algebraMap N (Work.MotC2.Func E) E.a₃ with hBdef
  set C : Work.MotC2.Func E := (Work.MotC2.genX E) ^ 3 +
      algebraMap N (Work.MotC2.Func E) E.a₂ * (Work.MotC2.genX E) ^ 2 +
      algebraMap N (Work.MotC2.Func E) E.a₄ * Work.MotC2.genX E +
      algebraMap N (Work.MotC2.Func E) E.a₆ with hCdef
  have hconst : ∀ c : N, algebraMap N (Work.MotC2.Func E) c ∈ S := fun c =>
    hKp _ (Work.MotV.algebraMap_mem_PthPow p E c)
  have hB : B ∈ S := by
    rw [hBdef]
    exact S.add_mem (S.mul_mem (hconst E.a₁) hx) (hconst E.a₃)
  have hC : C ∈ S := by
    rw [hCdef]
    exact S.add_mem (S.add_mem (S.add_mem (S.pow_mem hx 3)
      (S.mul_mem (hconst E.a₂) (S.pow_mem hx 2))) (S.mul_mem (hconst E.a₄) hx)) (hconst E.a₆)
  have hy2 : (Work.MotC2.genY E) ^ 2 ∈ S := by
    have hm : (Work.MotC2.genY E) ^ 2 ∈ Work.MotV.PthPow (Work.MotC2.Func E) p := by
      subst hp2
      exact Work.MotV.mem_PthPow.mpr ⟨Work.MotC2.genY E, rfl⟩
    exact hKp _ hm
  have hrel := Work.MotC2.genY_sq_relation E
  have hBy : B * Work.MotC2.genY E = C - (Work.MotC2.genY E) ^ 2 := by
    rw [hBdef, hCdef]
    linear_combination (norm := first | refl_ring1 | ring1) hrel
  have : B⁻¹ * (B * Work.MotC2.genY E) ∈ S :=
    S.mul_mem (S.inv_mem hB) (by rw [hBy]; exact S.sub_mem hC hy2)
  rwa [inv_mul_cancel_left₀ he] at this

end Work.MotV
