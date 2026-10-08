import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.GlaubermanZJ.ZJ_family
import Submission.Work.GlaubermanZJ.ZJ_eq
import Submission.Work.GlaubermanZJ.isAbelianSubgroup_iff
import Submission.Work.PGroup.ZJ_characteristic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `N_G(P) ≤ N_G(Z(J(P)))` for the blueprint's `ZJ`

The blueprint's `ZJ P = J(P) ∩ C_G(J(P)) = Z(J(P))` (`Submission.Blueprint.ZJ`), the centre of
Thompson's subgroup of `P`.  This file proves

`Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Submission.Blueprint.ZJ P : Set G)`,

i.e. `Z(J(P))` is characteristic in `P` — the standard fact that `N_G(P)` normalizes
`J(P) = ZJ`-free characteristic subgroup of `P`, and then normalizes the centre `Z(J(P))`.

Since the construction `J(P)` here is the blueprint's (`⨆` over the abelian subgroups of `P` of
maximal order, *not* the finite-only `Work.PGroup.thompsonJ`), the argument is carried out for the
blueprint's definition directly.  It has three steps:

* `thompsonJ_eq_closure` : `J(P)` is the closure of the union of the `ZJfam P` family
  (`Work.GlaubermanZJ.ZJfam`) — this turns the `⨆` into a closure;
* `thompsonJ_map_conj_eq` : conjugation by `g ∈ N_G(P)` permutes that family
  (`ZJfam_map_conj`), hence preserves the closure, so `N_G(P) ≤ N_G(J(P))`;
* the centre of a subgroup is characteristic in it (`Work.PGroup.centerIn_conj`), so
  `N_G(J(P)) ≤ N_G(Z(J(P))) = N_G(ZJ P)`.

Everything is true in an arbitrary group: no finiteness hypothesis is used.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.GlaubermanZJ

variable {G : Type*} [Group G]

/-! ## 1. The family `ZJfam P` is invariant under `N_G(P)` -/

/-- Conjugation by an element of `N_G(P)` permutes the abelian subgroups of `P` of maximal order:
it preserves `≤ P`, abelianness and `Nat.card` (conjugation is a bijection). -/
theorem ZJfam_map_conj {P A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) (hA : ZJfam P A) :
    ZJfam P (A.map (MulAut.conj g).toMonoidHom) := by
  have hPh : P.map (MulAut.conj g).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hg' : g⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normalizer (P : Set G)).inv_mem hg
  have hPh' : P.map (MulAut.conj g⁻¹).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg'
  refine ⟨?_, ?_, ?_⟩
  · calc A.map (MulAut.conj g).toMonoidHom
        ≤ P.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hA.1
      _ = P := hPh
  · haveI : IsMulCommutative ↥A := isAbelianSubgroup_iff.mp hA.2.1
    exact isAbelianSubgroup_iff.mpr
      (Subgroup.map_isMulCommutative A (MulAut.conj g).toMonoidHom)
  · intro B hBP hBab
    have hcard : Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    rw [hcard]
    have hB'le : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ P := by
      calc B.map (MulAut.conj g⁻¹).toMonoidHom
          ≤ P.map (MulAut.conj g⁻¹).toMonoidHom := Subgroup.map_mono hBP
        _ = P := hPh'
    have hB'ab : Submission.Blueprint.IsAbelianSubgroup
        (B.map (MulAut.conj g⁻¹).toMonoidHom) := by
      haveI : IsMulCommutative ↥B := isAbelianSubgroup_iff.mp hBab
      exact isAbelianSubgroup_iff.mpr
        (Subgroup.map_isMulCommutative B (MulAut.conj g⁻¹).toMonoidHom)
    have hB'card : Nat.card (B.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card B :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    have := hA.2.2 (B.map (MulAut.conj g⁻¹).toMonoidHom) hB'le hB'ab
    rwa [hB'card] at this

/-! ## 2. `J(P)` as a closure -/

/-- The blueprint's Thompson subgroup is the closure of the union of the family `ZJfam P`. -/
theorem thompsonJ_eq_closure (P : Subgroup G) :
    Submission.Blueprint.thompsonJ P =
      Subgroup.closure {x | ∃ A : Subgroup G, ZJfam P A ∧ x ∈ A} := by
  refine le_antisymm ?_ ?_
  · change (⨆ (A : Subgroup G) (_ : ZJfam P A), A) ≤
      Subgroup.closure {x | ∃ A : Subgroup G, ZJfam P A ∧ x ∈ A}
    refine iSup_le fun A => iSup_le fun hA => ?_
    intro x hx
    exact Subgroup.subset_closure ⟨A, hA, hx⟩
  · rw [Subgroup.closure_le]
    rintro x ⟨A, hA, hx⟩
    exact le_iSup (f := fun A : Subgroup G => ⨆ (_ : ZJfam P A), A) A
      (le_iSup (f := fun _ : ZJfam P A => A) hA hx)

/-! ## 3. `J(P)` is invariant under `N_G(P)` -/

/-- `H.map (conj g) = gHg⁻¹`, stated as a pointwise action. -/
theorem map_conj_eq_smul (g : G) (H : Subgroup G) :
    H.map (MulAut.conj g).toMonoidHom = MulAut.conj g • H := by
  rw [Subgroup.pointwise_smul_def]; rfl

/-- Conjugation by `g ∈ N_G(P)` fixes the blueprint's Thompson subgroup `J(P)`. -/
theorem thompsonJ_map_conj_eq (P : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    (Submission.Blueprint.thompsonJ P).map (MulAut.conj g).toMonoidHom =
      Submission.Blueprint.thompsonJ P := by
  have hg' : g⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normalizer (P : Set G)).inv_mem hg
  set T : Set G := {x | ∃ A : Subgroup G, ZJfam P A ∧ x ∈ A} with hT
  have hJ : Submission.Blueprint.thompsonJ P = Subgroup.closure T := thompsonJ_eq_closure P
  have himg : (MulAut.conj g) • T ⊆ T := by
    intro y hy
    rw [Set.mem_smul_set] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨A, hA, hxA⟩ := hx
    exact ⟨A.map (MulAut.conj g).toMonoidHom, ZJfam_map_conj hg hA,
      Subgroup.mem_map_of_mem _ hxA⟩
  have himg' : (MulAut.conj g⁻¹) • T ⊆ T := by
    intro y hy
    rw [Set.mem_smul_set] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨A, hA, hxA⟩ := hx
    exact ⟨A.map (MulAut.conj g⁻¹).toMonoidHom, ZJfam_map_conj hg' hA,
      Subgroup.mem_map_of_mem _ hxA⟩
  have hle : (Submission.Blueprint.thompsonJ P).map (MulAut.conj g).toMonoidHom ≤
      Submission.Blueprint.thompsonJ P := by
    rw [hJ, map_conj_eq_smul g, Subgroup.smul_closure]
    exact Subgroup.closure_mono himg
  have hsub : T ⊆ (MulAut.conj g) • T := by
    intro x hx
    refine ⟨(MulAut.conj g⁻¹) • x, himg' (Set.mem_smul_set.mpr ⟨x, hx, rfl⟩), ?_⟩
    simp only [MulAut.smul_def, MulAut.conj_apply]
    group
  have hge : Submission.Blueprint.thompsonJ P ≤
      (Submission.Blueprint.thompsonJ P).map (MulAut.conj g).toMonoidHom := by
    rw [hJ, map_conj_eq_smul g, Subgroup.smul_closure]
    exact Subgroup.closure_mono hsub
  exact le_antisymm hle hge

/-- `N_G(P) ≤ N_G(J(P))`. -/
theorem normalizer_le_normalizer_thompsonJ (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (Submission.Blueprint.thompsonJ P : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact thompsonJ_map_conj_eq P g hg

/-! ## 4. The centre of a subgroup is characteristic in it -/

/-- `N_G(H) ≤ N_G(Z(H))`: conjugation by an element of `N_G(H)` is an automorphism of `H`, so it
carries `Z(H)` onto `Z(H)` (`Work.PGroup.centerIn_conj`). -/
theorem normalizer_le_normalizer_centerIn (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (Work.PGroup.centerIn H : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  have hcm : Subgroup.map (↑(MulAut.conj g) : G →* G) (Work.PGroup.centerIn H) =
      Work.PGroup.centerIn (Subgroup.map (↑(MulAut.conj g) : G →* G) H) :=
    Work.PGroup.centerIn_conj g H
  rw [hcm, hg]

/-! ## 5. The target -/

/-- `N_G(J(P)) ≤ N_G(Z(J(P))) = N_G(ZJ(P))`, via the bridge
`ZJ P = centerIn (thompsonJ P)`. -/
theorem normalizer_ZJ_of_normalizer_thompsonJ (P : Subgroup G) :
    Subgroup.normalizer (Submission.Blueprint.thompsonJ P : Set G) ≤
      Subgroup.normalizer (Submission.Blueprint.ZJ P : Set G) := by
  have hZJ : Submission.Blueprint.ZJ P =
      Work.PGroup.centerIn (Submission.Blueprint.thompsonJ P) :=
    inf_centralizer_eq_centerIn _
  rw [hZJ]
  exact normalizer_le_normalizer_centerIn _

theorem normalizer_ZJ {G : Type*} [Group G] (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (Submission.Blueprint.ZJ P : Set G) :=
  le_trans (normalizer_le_normalizer_thompsonJ P)
    (normalizer_ZJ_of_normalizer_thompsonJ P)

end Work.GlaubermanZJ
