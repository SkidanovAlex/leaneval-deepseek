import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.A_quot_irreducible

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- **Higman 1963, Lemma 8 — step 2 (squaring is onto).**  In the situation of Higman's Lemma 8
(`A` a normal `ξ`-invariant abelian subgroup, `C` a normal `ξ`-invariant subgroup covering `A`,
`C ^ (2) ≤ A`, `⁅C,C⁆ = A`) with `A` non-trivial, the squaring map `C / A → A / A²` is onto:
`C ^ (2) = A`.  This is the step that makes the lower central series of `C` equal to
`C > A > A² > A⁴ > ⋯`, which is what Higman's Lemma 8 uses. -/
theorem powSub_C_eq_of_cover {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCd : ⁅C, C⁆ = A) (hAne : A ≠ ⊥) :
    Work.Higman.powSub C 2 = A := by
  have hCinv' := hCinv
  -- `C ^ (2)` is `ξ`-invariant and lies between `A ^ (2)` and `A`
  have hDinv : (powSub C 2).map (h.xi : MulAut P).toMonoidHom = powSub C 2 :=
    map_powSub (h.xi : MulAut P) hCinv' 2
  have hA2le : powSub A 2 ≤ powSub C 2 := powSub_mono hAC
  rcases xi_invariant_eq_powSub_two_or_self h hA hC2 hA2le hDinv with hcase | hcase
  · -- `C ^ (2) = A ^ (2)` is impossible
    exfalso
    -- the commutator pairing vanishes
    have hcomm : ⁅C, C⁆ ≤ powSub A 2 := by
      rw [Subgroup.commutator_le]
      intro u hu v hv
      have hχ : ⁅u, ⁅v, u⁆⁆ ∈ powSub A 2 :=
        commutator_mem_powSub_two h hA u ⁅v, u⁆ (by
          rw [← hCd]
          exact Subgroup.commutator_mem_commutator hv hu)
      have hone : (u * v) * (u * v) = ⁅u, ⁅v, u⁆⁆ * (⁅v, u⁆ * (u * u) * (v * v)) := by
        simp only [commutatorElement_def]
        group
      have hm1 : (u * v) * (u * v) ∈ powSub A 2 := by
        have h2 : (u * v) ^ 2 ∈ powSub A 2 := by
          rw [← hcase]
          exact pow_mem_powSub (A := C) (C.mul_mem hu hv)
        simpa [pow_two] using h2
      have hmu : u * u ∈ powSub A 2 := by
        have h2 : u ^ 2 ∈ powSub A 2 := by
          rw [← hcase]
          exact pow_mem_powSub (A := C) hu
        simpa [pow_two] using h2
      have hmv : v * v ∈ powSub A 2 := by
        have h2 : v ^ 2 ∈ powSub A 2 := by
          rw [← hcase]
          exact pow_mem_powSub (A := C) hv
        simpa [pow_two] using h2
      have h3 : ⁅v, u⁆ = (⁅u, ⁅v, u⁆⁆)⁻¹ * ((u * v) * (u * v))
          * ((v * v)⁻¹ * (u * u)⁻¹) := by
        rw [hone]
        group
      have hmem : ⁅v, u⁆ ∈ powSub A 2 := by
        rw [h3]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ((powSub A 2).inv_mem hχ) hm1)
          (Subgroup.mul_mem _ ((powSub A 2).inv_mem hmv) ((powSub A 2).inv_mem hmu))
      have hsym : ⁅u, v⁆ = (⁅v, u⁆)⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]
        group
      rw [hsym]
      exact (powSub A 2).inv_mem hmem
    rw [hCd] at hcomm
    have hA2 : A = powSub A 2 := le_antisymm hcomm (powSub_le (by norm_num))
    -- `A = A ^ (2 ^ k)` for every `k`, and `A ^ (2 ^ n) = ⊥` because `A` is a finite `2`-group
    have hIter : ∀ k, A = powSub A (2 ^ k) := by
      intro k
      induction k with
      | zero => rw [pow_zero, powSub_one_eq]
      | succ k ih =>
          rw [pow_succ, ← powSub_powSub hA.abelian, ← ih, ← hA2]
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (h.isPGroup.to_subgroup A)
    have hbot : powSub A (2 ^ n) = ⊥ := by
      refine powSub_eq_bot_of_exp hA.abelian le_rfl fun x hx => ?_
      haveI : Fintype ↥A := Fintype.ofFinite _
      have hxA : orderOf (⟨x, hx⟩ : ↥A) ∣ 2 ^ n := by
        have h := orderOf_dvd_card (x := (⟨x, hx⟩ : ↥A))
        rwa [← Nat.card_eq_fintype_card, hn] at h
      have h1 : (⟨x, hx⟩ : ↥A) ^ 2 ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp hxA
      simpa [Subgroup.coe_pow] using congrArg (fun t : ↥A => (t : P)) h1
    exact hAne (by rw [hIter n, hbot])
  · exact hcase

end Work.Higman
