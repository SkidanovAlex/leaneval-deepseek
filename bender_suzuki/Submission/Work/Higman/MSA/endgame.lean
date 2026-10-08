/-
Copyright (c) 2024. All rights reserved.

# Higman (1963), Lemma 9: the endgame

Higman's Lemma 9, second part: for a maximal `ξ`-invariant abelian normal subgroup `A` of a
Suzuki 2-group, `Φ(P) ≤ A`.  The argument (Higman §5) goes through a minimal covering `C > A`
with `C ≤ A · Φ(P)` and uses the `Φ(C) ∈ {A², A}` dichotomy; see
`Submission/Work/Higman/MSA_NOTES.md` §4.

This file contains the auxiliary fact that `Φ(P)` centralizes `A` when `A⁴ = ⊥`, proved by
elementary commutator calculus (unipotence `commutator_mem_powSub_two` applied to `A` and to
`A²`, which is *ξ*-abelian-normal).
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.MSA.basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Higman.MSA

open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

/-- `A²` is `ξ`-abelian-normal when `A` is. -/
theorem isXiAbelNormal_powSub_two {h : IsSuzuki2Grp P} {A : Subgroup P}
    (hA : IsXiAbelNormal h A) : IsXiAbelNormal h (powSub A 2) := by
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  have hconj : ∀ g : P, A.map (MulAut.conj g).toMonoidHom = A :=
    (Subgroup.normal_iff_map_conj_eq.mp hA.normal)
  refine ⟨?_, Work.Higman.map_powSub (h.xi : MulAut P) hA.map_eq 2, ?_⟩
  · refine (Subgroup.normal_iff_map_conj_eq).mpr (fun g => ?_)
    exact Work.Higman.map_powSub (MulAut.conj g) (hconj g) 2
  · exact Work.Higman.powSub_comm hAb 2

/-- **`Φ(P)` centralizes `A` when `A⁴ = ⊥`.**  If `A` is a `ξ`-invariant abelian normal subgroup
of a Suzuki 2-group with `powSub A 4 = ⊥`, then `Φ(P) = P²·[P,P]` lies in the centralizer of `A`.

Proof.  Unipotence gives `[P,A] ⊆ A²`; applying unipotence to the `ξ`-abelian-normal subgroup
`A²` (and `powSub_powSub`, `powSub A 4 = ⊥`) gives `A² ≤ Z(P)`.  Hence for `a ∈ A` and `g ∈ P`,
`[a,g²] = [a,g]·[a,g]^g = [a,g]² = 1`, so `P² ≤ C_P(A)`.  For fixed `a`, the map
`g ↦ [a,g]` is a homomorphism `P → A²` (using `[a,gh] = [a,g][a,h]^g` and `A² ≤ Z(P)`), with
abelian target, so `P'` lies in its kernel: `[a,[g,h]] = 1` for all `g,h`, i.e. `P' ≤ C_P(A)`. -/
theorem commutator_frattini_centralizes {h : IsSuzuki2Grp P} {A : Subgroup P}
    (hA : IsXiAbelNormal h A) (h4 : powSub A 4 = ⊥) :
    powSub (⊤ : Subgroup P) 2 ⊔ ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.centralizer (A : Set P) := by
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  have hA2 : IsXiAbelNormal h (powSub A 2) := isXiAbelNormal_powSub_two hA
  -- `A² ≤ Z(P)`: unipotence applied to `A²`
  have hA2center : powSub A 2 ≤ Subgroup.center P := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : ⁅y, x⁆ ∈ powSub (powSub A 2) 2 :=
      Work.Higman.commutator_mem_powSub_two h hA2 y x hx
    have h2 : powSub (powSub A 2) 2 = powSub A 4 := by
      have := Work.Higman.powSub_powSub hAb 2 2
      simpa using this
    rw [h2] at h1
    rw [h4] at h1
    simp only [Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  -- `[A,P] ⊆ A²`: unipotence
  have hAP : ∀ a ∈ A, ∀ u : P, ⁅a, u⁆ ∈ powSub A 2 := by
    intro a ha u
    have h1 : ⁅u, a⁆ ∈ powSub A 2 := Work.Higman.commutator_mem_powSub_two h hA u a ha
    have h2 : ⁅a, u⁆ = ⁅u, a⁆⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rw [h2]
    exact (powSub A 2).inv_mem h1
  -- `P² ≤ C_P(A)`
  have hP2 : powSub (⊤ : Subgroup P) 2 ≤ Subgroup.centralizer (A : Set P) := by
    have hsq : ∀ g : P, g * g ∈ Subgroup.centralizer (A : Set P) := by
      intro g
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      -- `[a, g * g] = [a,g] * [a,g]^g = [a,g] * [a,g] = 1`
      have hkey : ⁅a, g * g⁆ = ⁅a, g⁆ * (g * ⁅a, g⁆ * g⁻¹) := by
        rw [commutatorElement_def, commutatorElement_def]; group
      have hmem : ⁅a, g⁆ ∈ powSub A 2 := hAP a ha g
      have hcomm : g * ⁅a, g⁆ * g⁻¹ = ⁅a, g⁆ := by
        have hc : ⁅a, g⁆ ∈ Subgroup.center P := hA2center hmem
        rw [Subgroup.mem_center_iff] at hc
        calc g * ⁅a, g⁆ * g⁻¹ = (⁅a, g⁆ * g) * g⁻¹ := by rw [hc g]
          _ = ⁅a, g⁆ := by group
      have hsqz : ⁅a, g⁆ * ⁅a, g⁆ = 1 := by
        have h2 : ⁅a, g⁆ * ⁅a, g⁆ ∈ powSub (powSub A 2) 2 := by
          rw [show ⁅a, g⁆ * ⁅a, g⁆ = (⁅a, g⁆) ^ 2 from (pow_two _).symm]
          exact Work.Higman.pow_mem_powSub hmem
        have h3 : powSub (powSub A 2) 2 = powSub A 4 := by
          have := Work.Higman.powSub_powSub hAb 2 2
          simpa using this
        rw [h3, h4] at h2
        simpa using h2
      have h1 : ⁅a, g * g⁆ = 1 := by rw [hkey, hcomm, hsqz]
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    have hsub : {y : P | ∃ x ∈ (⊤ : Subgroup P), x ^ 2 = y} ⊆
        (Subgroup.centralizer (A : Set P) : Set P) := by
      rintro y ⟨x, -, rfl⟩
      simpa [pow_two] using hsq x
    have := (Subgroup.closure_le (Subgroup.centralizer (A : Set P))).mpr hsub
    simpa [Work.Higman.powSub] using this
  -- `P' ≤ C_P(A)`
  have hPd : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.centralizer (A : Set P) := by
    rw [Subgroup.commutator_le]
    intro g _ g' _
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    -- the map `u ↦ [a,u]` is a homomorphism `P →* P` with image in the abelian `A²`
    have hhom : ∀ u v : P, ⁅a, u * v⁆ = ⁅a, u⁆ * ⁅a, v⁆ := by
      intro u v
      have hkey : ⁅a, u * v⁆ = ⁅a, u⁆ * (u * ⁅a, v⁆ * u⁻¹) := by
        rw [commutatorElement_def, commutatorElement_def]; group
      rw [hkey]
      have hmem : ⁅a, v⁆ ∈ powSub A 2 := hAP a ha v
      have hc : ⁅a, v⁆ ∈ Subgroup.center P := hA2center hmem
      have : u * ⁅a, v⁆ * u⁻¹ = ⁅a, v⁆ := by
        rw [Subgroup.mem_center_iff] at hc
        calc u * ⁅a, v⁆ * u⁻¹ = (⁅a, v⁆ * u) * u⁻¹ := by rw [hc u]
          _ = ⁅a, v⁆ := by group
      rw [this]
    let f : P →* P := MonoidHom.mk' (fun u : P => ⁅a, u⁆) hhom
    have hfmem : ∀ u : P, f u ∈ powSub A 2 := fun u => hAP a ha u
    have hA2ab : ∀ x ∈ powSub A 2, ∀ y ∈ powSub A 2, x * y = y * x := hA2.abelian
    have hker : ⁅g, g'⁆ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hA2ab _ (hfmem g) _ (hfmem g'))
    exact commutatorElement_eq_one_iff_mul_comm.mp hker
  exact sup_le hP2 hPd

end Work.Higman.MSA
