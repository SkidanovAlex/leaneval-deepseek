import Mathlib
import Submission.Work.Higman.clo_hard_defs
import Submission.Work.Higman.powSub_C_eq_of_cover
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.squaring_layer
import Submission.Work.Higman.bracket_expansion
import Submission.Work.Higman.Fq_structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Auxiliary lemmas for `cloSM`

Elementary properties of the power map `cloSM : C/A → Ω₁(P)` and of the automorphisms
`cloXiOm`, `cloXiQuot` induced by `ξ`: the value on `1`, the `ξ`-equivariance (and its
iterates), transitivity of `ξ` on `Ω₁(P) ∖ {1}`, and the fact that `cloSM` does not vanish
identically.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

variable {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]

section Quot

/-- `cloXiQuot` on the class of a representative. -/
theorem cloXiQuot_mk (h : IsSuzuki2Grp P) (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (u : ↥C) :
    cloXiQuot h hAinv hCinv (QuotientGroup.mk u) = QuotientGroup.mk (cloXiC h hCinv u) :=
  QuotientGroup.congr_mk _ _ _ _ u

/-- `cloSM 1 = 1`. -/
theorem cloSM_one (S : CloH8Data h A C) : cloSM S 1 = 1 := by
  have h1 : (1 : ↥C ⧸ (A.subgroupOf C)) = QuotientGroup.mk (1 : ↥C) :=
    (QuotientGroup.mk_one _).symm
  apply Subtype.ext
  rw [h1, cloSM_mk]
  simp

/-- `cloSM` is `ξ`-equivariant. -/
theorem cloSM_xi (S : CloH8Data h A C) (x : ↥C ⧸ (A.subgroupOf C)) :
    cloXiOm h (cloSM S x) = cloSM S (cloXiQuot h S.hA.map_eq S.hCinv x) := by
  induction x using QuotientGroup.induction_on with
  | _ u =>
    apply Subtype.ext
    rw [cloXiOm_apply, cloXiQuot_mk, cloSM_mk, cloSM_mk, map_pow, cloXiSub_apply]

/-- The iterated `ξ`-equivariance of `cloSM`. -/
theorem cloSM_xi_pow (S : CloH8Data h A C) (k : ℕ) (x : ↥C ⧸ (A.subgroupOf C)) :
    ((cloXiOm h) ^ k) (cloSM S x)
      = cloSM S (((cloXiQuot h S.hA.map_eq S.hCinv) ^ k) x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : ((cloXiOm h) ^ (k + 1)) (cloSM S x)
        = (cloXiOm h) (((cloXiOm h) ^ k) (cloSM S x)) := by rw [pow_succ']; rfl
    have h2 : ((cloXiQuot h S.hA.map_eq S.hCinv) ^ (k + 1)) x
        = (cloXiQuot h S.hA.map_eq S.hCinv) (((cloXiQuot h S.hA.map_eq S.hCinv) ^ k) x) := by
      rw [pow_succ']; rfl
    rw [h1, h2, ih, cloSM_xi]

end Quot

/-- `ξ` acts transitively on the non-identity elements of `Ω₁(P)`. -/
theorem cloXiOm_trans (h : IsSuzuki2Grp P) {z w : ↥(omega1 P)} (hz : z ≠ 1) (hw : w ≠ 1) :
    ∃ k : ℕ, ((cloXiOm h) ^ k) z = w := by
  have hz2 : orderOf (z : P) = 2 :=
    orderOf_eq_two_of_mem_omega1 h z.2 (fun hc => hz (Subtype.ext hc))
  have hw2 : orderOf (w : P) = 2 :=
    orderOf_eq_two_of_mem_omega1 h w.2 (fun hc => hw (Subtype.ext hc))
  obtain ⟨k, hk⟩ := h.trans (z : P) (w : P) hz2 hw2
  exact ⟨k, Subtype.ext (by rw [cloXiOm_pow_apply]; exact hk)⟩

/-- `cloSM` does not vanish identically: some element of `C/A` has a non-trivial image. -/
theorem cloSM_exists_ne_one (S : CloH8Data h A C) :
    ∃ x : ↥C ⧸ (A.subgroupOf C), cloSM S x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ u : ↥C, (u : P) ^ 2 ^ S.e = 1 := by
    intro u
    have h1 := congrArg (fun t : ↥(omega1 P) => (t : P)) (hcon (QuotientGroup.mk u))
    rwa [cloSM_mk, Subgroup.coe_one] at h1
  -- every square in `C` lies in `A ^ 2`
  have hsq : ∀ u : ↥C, (u : P) ^ 2 ∈ powSub A 2 := by
    intro u
    have hu2A : (u : P) ^ 2 ∈ A := by
      simpa [pow_two] using sq_mem_A S.hC2 u.2
    have hpow : ((u : P) ^ 2) ^ 2 ^ (S.e - 1) = 1 := by
      rw [← pow_mul, show 2 * 2 ^ (S.e - 1) = 2 ^ S.e from by
        rw [mul_comm, ← pow_succ, Nat.sub_add_cancel S.he]]
      exact hall u
    exact (S.hkey _ hu2A).mpr hpow
  have hle : powSub C 2 ≤ powSub A 2 := by
    rw [powSub, Subgroup.closure_le]
    rintro x ⟨u, hu, rfl⟩
    exact hsq ⟨u, hu⟩
  have hC2eq : powSub C 2 = A :=
    powSub_C_eq_of_cover h S.hA S.hCn S.hCinv S.hAC S.hCA S.hcover S.hC2 S.hCd S.hAne
  have hA : A = powSub A 2 :=
    le_antisymm (hC2eq ▸ hle) (powSub_le (by norm_num))
  -- hence `A = A ^ (2 ^ k)` for every `k`
  have hiter : ∀ k : ℕ, A = powSub A (2 ^ k) := by
    intro k
    induction k with
    | zero => rw [pow_zero, powSub_one_eq]
    | succ j ih =>
      have hstep : powSub A (2 ^ (j + 1)) = powSub (powSub A (2 ^ j)) 2 := by
        rw [pow_succ]
        exact (powSub_powSub S.hA.abelian (2 ^ j) 2).symm
      rw [hstep, ← ih]
      exact hA
  have hbot : A = ⊥ := by
    rw [hiter S.e, powSub_eq_bot_of_exp S.hA.abelian (k := S.e) (le_refl S.e) S.he1]
  exact S.hAne hbot

end Work.Higman
