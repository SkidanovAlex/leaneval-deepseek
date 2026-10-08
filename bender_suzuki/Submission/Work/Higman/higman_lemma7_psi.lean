import Mathlib
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.Defs
import Submission.Work.Higman.homogeneous_structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {P : Type} [Group P]

/-- `powSub A n ≤ A` for every `n` (including `n = 0`). -/
theorem powSub_le_self (A : Subgroup P) (n : ℕ) : powSub A n ≤ A := by
  rcases Nat.eq_zero_or_pos n with h | h
  · rw [h, powSub_zero]; exact bot_le
  · exact powSub_le h

/-- With `C' = A ^ (2 ^ s)`, `s ≤ e - 1`, and `2 ^ e` the exponent of the abelian `A`, the
map `v ↦ v ^ 2 ^ (e-1-s)` is a `ξ`-equivariant homomorphism of `C'` into `A ⊓ Ω₁` with
kernel `(C')²` (where `(C')² = powSub C' 2`). -/
theorem higman_lemma7_psi {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    {e s : ℕ} (hse : s ≤ e - 1)
    (hkeyk : ∀ k ≤ e, ∀ y ∈ A, y ∈ Work.Higman.powSub A (2 ^ k) ↔ y ^ 2 ^ (e - k) = 1)
    (hker : Work.Higman.powSub A (2 ^ (e - 1)) = A ⊓ Work.Higman.omega1 P)
    (hDs : ⁅C, C⁆ = Work.Higman.powSub A (2 ^ s)) :
    (∀ v ∈ ⁅C, C⁆, v ^ 2 ^ (e - 1 - s) ∈ A ⊓ Work.Higman.omega1 P) ∧
      (∀ u ∈ ⁅C, C⁆, ∀ v ∈ ⁅C, C⁆,
        (u * v) ^ 2 ^ (e - 1 - s) = u ^ 2 ^ (e - 1 - s) * v ^ 2 ^ (e - 1 - s)) ∧
      (∀ v ∈ ⁅C, C⁆, v ^ 2 ^ (e - 1 - s) = 1 ↔ v ∈ Work.Higman.powSub ⁅C, C⁆ 2) ∧
      (∀ v ∈ ⁅C, C⁆, h.xi (v ^ 2 ^ (e - 1 - s)) = (h.xi v) ^ 2 ^ (e - 1 - s)) := by
  classical
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  have hpow : powSub ⁅C, C⁆ 2 = powSub A (2 ^ (s + 1)) := by
    rw [hDs, powSub_powSub hAb (2 ^ s) 2, ← pow_succ]
  have hCle : ⁅C, C⁆ ≤ A := by
    rw [hDs]; exact powSub_le_self A (2 ^ s)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    have hv' : v ∈ powSub A (2 ^ s) := by rw [← hDs]; exact hv
    obtain ⟨a, ha, hae⟩ := (mem_powSub_iff hAb).mp hv'
    rw [← hae, ← pow_mul, ← pow_add, Nat.add_sub_of_le hse, ← hker]
    exact pow_mem_powSub ha
  · intro u hu v hv
    exact Commute.mul_pow (hAb u (hCle hu) v (hCle hv)) (2 ^ (e - 1 - s))
  · intro v hv
    rw [hpow]
    have hvA : v ∈ A := hCle hv
    rcases Nat.eq_zero_or_pos e with he0 | hepos
    · subst he0
      have hs0 : s = 0 := by omega
      subst hs0
      have hAbot : A = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro y hy
        have hmem : y ∈ powSub A (2 ^ 0) := by rw [pow_zero, powSub_one_eq]; exact hy
        have hh := (hkeyk 0 (Nat.zero_le 0) y hy).mp hmem
        simpa using hh
      have hv1 : v = 1 := by
        have : v ∈ (⊥ : Subgroup P) := by rw [← hAbot]; exact hvA
        simpa using this
      subst hv1
      simp
    · have hk : s + 1 ≤ e := by omega
      have hkey := hkeyk (s + 1) hk v hvA
      have hsub : e - (s + 1) = e - 1 - s := by omega
      rw [hsub] at hkey
      exact hkey.symm
  · intro v hv
    exact map_pow (h.xi : MulAut P).toMonoidHom v (2 ^ (e - 1 - s))

end Work.Higman
