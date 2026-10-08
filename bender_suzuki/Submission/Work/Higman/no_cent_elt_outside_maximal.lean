/-
Copyright (c) 2024. All rights reserved.

# No central element of a `ξ`-invariant normal subgroup lies outside a maximal one

Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), 79--96, §3
(`REFS/higman_suzuki2groups.md`).

Let `P` be a Suzuki 2-group, `A` a *maximal* `ξ`-invariant abelian normal subgroup of `P`
(maximal in the family `IsXiAbelNormal h`), and `D ⊵ A` a `ξ`-invariant normal subgroup of `P`.
Then no element `z ∈ D` that lies in the centre of `D` can lie outside `A`: such a `z`, together
with `A`, generates the strictly larger `ξ`-invariant abelian normal subgroup

`A ⊔ (D ⊓ C_P(D))`,

where `D ⊓ C_P(D)` is the centre `Z(D)` computed inside `P`, contradicting maximality of `A`.
(The hypothesis `hcomm` — that all commutators of `P` lie in `A` — is not needed for this step;
it is kept because it is part of the interface used by the caller.)

Mathlib does not name the subgroup `Z(D)` of `P`, so the object used below is
`Z := D ⊓ Subgroup.centralizer (D : Set P)`, whose elements are exactly the elements of `D`
commuting with all of `D`.  The two technical inputs are proved first:

* `map_inf_centralizer_eq`: an automorphism carrying `D` onto itself carries `Z` onto itself;
* `sup_inf_centralizer_comm`: `A ⊔ Z` is abelian when `A ≤ D` is abelian.
-/
import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

/-- An automorphism of `P` carrying the subgroup `D` onto itself carries `D ⊓ C_P(D)` onto
itself.  (`D ⊓ C_P(D)` is the centre of `D` viewed as a subgroup of `P`.) -/
theorem map_inf_centralizer_eq {P : Type} [Group P] {D : Subgroup P} (φ : MulAut P)
    (hDφ : D.map (φ : MulAut P).toMonoidHom = D) :
    (D ⊓ Subgroup.centralizer (D : Set P)).map (φ : MulAut P).toMonoidHom
      = D ⊓ Subgroup.centralizer (D : Set P) := by
  set F : P →* P := (φ : MulAut P).toMonoidHom with hF
  set F' : P →* P := (φ.symm : MulAut P).toMonoidHom with hF'
  have hDφF : D.map F = D := hDφ
  have hDφF' : D.map F' = D := by
    have h := Subgroup.map_map D F' F
    rw [hDφF] at h
    have hc : F'.comp F = MonoidHom.id P := by rw [hF, hF']; ext x; simp
    rw [hc, Subgroup.map_id] at h
    exact h
  have hFinj : Function.Injective ⇑F := by rw [hF]; exact φ.injective
  have hcomp : F.comp F' = MonoidHom.id P := by rw [hF, hF']; ext x; simp
  have hC_le : (Subgroup.centralizer (D : Set P)).map F ≤ Subgroup.centralizer (D : Set P) := by
    refine le_trans (Subgroup.map_centralizer_le_centralizer_image (D : Set P) F) ?_
    have h : ⇑F '' (D : Set P) = D := by
      rw [← Subgroup.coe_map (f := F), hDφF]
    rw [h]
  have hC'_le : (Subgroup.centralizer (D : Set P)).map F' ≤
      Subgroup.centralizer (D : Set P) := by
    refine le_trans (Subgroup.map_centralizer_le_centralizer_image (D : Set P) F') ?_
    have h : ⇑F' '' (D : Set P) = D := by
      rw [← Subgroup.coe_map (f := F'), hDφF']
    rw [h]
  have hCeq : (Subgroup.centralizer (D : Set P)).map F = Subgroup.centralizer (D : Set P) := by
    refine le_antisymm hC_le ?_
    calc Subgroup.centralizer (D : Set P)
        = Subgroup.map F (Subgroup.map F' (Subgroup.centralizer (D : Set P))) := by
          rw [Subgroup.map_map, hcomp, Subgroup.map_id]
      _ ≤ Subgroup.map F (Subgroup.centralizer (D : Set P)) := Subgroup.map_mono hC'_le
  rw [Subgroup.map_inf D (Subgroup.centralizer (D : Set P)) F hFinj, hDφF, hCeq]

/-- If `A` is an abelian subgroup of `D`, then `A ⊔ (D ⊓ C_P(D))` is abelian: `D ⊓ C_P(D)` is
the centre of `D` (hence abelian, and centralising `A ≤ D`), and every element of it commutes
with every element of `A`. -/
theorem sup_inf_centralizer_comm {P : Type} [Group P] {A D : Subgroup P}
    (hAD : A ≤ D) (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    ∀ x ∈ A ⊔ (D ⊓ Subgroup.centralizer (D : Set P)),
      ∀ y ∈ A ⊔ (D ⊓ Subgroup.centralizer (D : Set P)), x * y = y * x := by
  set Z : Subgroup P := D ⊓ Subgroup.centralizer (D : Set P) with hZ
  have hZleD : Z ≤ D := by rw [hZ]; exact inf_le_left
  have hZleC : Z ≤ Subgroup.centralizer (D : Set P) := by rw [hZ]; exact inf_le_right
  have hZleCA : Z ≤ Subgroup.centralizer (A : Set P) :=
    le_trans hZleC (Subgroup.centralizer_le hAD)
  have hAA : A ≤ Subgroup.centralizer (A : Set P) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    exact fun y hy => hAab y hy x hx
  have hZZ : Z ≤ Subgroup.centralizer (Z : Set P) :=
    le_trans hZleC (Subgroup.centralizer_le hZleD)
  have hAZ : A ≤ Subgroup.centralizer (Z : Set P) := Subgroup.le_centralizer_iff.mpr hZleCA
  have hcent : A ⊔ Z ≤ Subgroup.centralizer ((A ⊔ Z : Subgroup P) : Set P) :=
    sup_le (Subgroup.le_centralizer_iff.mpr (sup_le hAA hZleCA))
           (Subgroup.le_centralizer_iff.mpr (sup_le hAZ hZZ))
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (hcent hx) y hy).symm

theorem no_cent_elt_outside_maximal {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hDn : D.Normal) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAD : A ≤ D) (hcomm : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ A)
    {z : P} (hzD : z ∈ D) (hzc : ∀ y ∈ D, y * z = z * y) (hzA : z ∉ A) :
    False := by
  have hAn : A.Normal := hA.normal
  have hDn' : D.Normal := hDn
  have hZnorm : (D ⊓ Subgroup.centralizer (D : Set P)).Normal :=
    Subgroup.normal_inf_normal D (Subgroup.centralizer (D : Set P))
  have hZxi : (D ⊓ Subgroup.centralizer (D : Set P)).map (h.xi : MulAut P).toMonoidHom
      = D ⊓ Subgroup.centralizer (D : Set P) :=
    map_inf_centralizer_eq (h.xi : MulAut P) hDinv
  have hB : IsXiAbelNormal h (A ⊔ (D ⊓ Subgroup.centralizer (D : Set P))) :=
    ⟨Subgroup.sup_normal A (D ⊓ Subgroup.centralizer (D : Set P)),
      by rw [Subgroup.map_sup, hA.map_eq, hZxi],
      sup_inf_centralizer_comm hAD hA.abelian⟩
  have hzZ : z ∈ D ⊓ Subgroup.centralizer (D : Set P) :=
    ⟨hzD, Subgroup.mem_centralizer_iff.mpr hzc⟩
  have hzB : z ∈ A ⊔ (D ⊓ Subgroup.centralizer (D : Set P)) :=
    (le_sup_right : (D ⊓ Subgroup.centralizer (D : Set P)) ≤
      A ⊔ (D ⊓ Subgroup.centralizer (D : Set P))) hzZ
  have hEq : A ⊔ (D ⊓ Subgroup.centralizer (D : Set P)) = A :=
    hmax (A ⊔ (D ⊓ Subgroup.centralizer (D : Set P))) hB le_sup_left
  exact hzA (hEq ▸ hzB)

end Work.Higman
