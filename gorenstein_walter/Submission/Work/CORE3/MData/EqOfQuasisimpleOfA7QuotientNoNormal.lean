import Mathlib
import Submission.Work.CORE3.Defs

/-!
# Uniqueness of the `A₇`-quasisimple subgroup (no normality needed)

The CORE3 §3 `M`-analysis needs: if `E ≤ E'` are quasisimple subgroups of a finite group and both
central quotients `E/Z(E)`, `E'/Z(E')` are isomorphic to `A₇`, then `E = E'`; the version used in
`Work.CORE3.MDataLocalControlOddCore` applies this to `E = E(M)` and `E' = E(N)` for subgroups
`M ≤ N` that are *not* assumed normal in the ambient group, so no normality hypothesis may be
used here.

The mathematical content is the elementary fact that a perfect group is determined by its
central quotient.

* If `E ≤ E'` are subgroups of a finite group, `Z = Z(E')`, then the composite map
  `↥E → ↥E' → ↥E'/Z` has kernel contained in `Z(E)`, so its image has order at least
  `|E|/|Z(E)| = |E'/Z|`; hence it is onto and `E' = E Z(E')`.
* But then, since `Z(E')` is central, `⁅E',E'⁆ = ⁅E Z(E'), E Z(E')⁆ = ⁅E,E⁆`, and both groups are
  perfect: `E' = ⁅E',E'⁆ = ⁅E,E⁆ = E`.

This is exactly what is formalised below (`eq_of_le_of_card_quotient_center_eq`), the requested
statement being its immediate corollary.

Reference: Gorenstein–Walter, *The characterization of finite groups with dihedral Sylow
2-subgroups*, J. Algebra 2 (1965), §3.
-/

namespace Work.CORE3.MData

open Subgroup

open scoped commutatorElement

/-- If `Z` centralizes `H ⊔ Z`, then every element of `H ⊔ Z` is of the form `h * z`, `h ∈ H`,
`z ∈ Z`.

Work in the group `↥(H ⊔ Z)`: there `Z` is contained in the centre, hence normal, and
`H ⊔ Z = ⊤`, so the standard description of the join of a subgroup and a normal subgroup
applies. -/
private lemma exists_mul_of_mem_sup_of_le_centralizer {X : Type*} [Group X] {H Z : Subgroup X}
    (hZ : Z ≤ Subgroup.centralizer ((H ⊔ Z : Subgroup X) : Set X)) {x : X} (hx : x ∈ H ⊔ Z) :
    ∃ h ∈ H, ∃ z ∈ Z, h * z = x := by
  have hHle : H ≤ H ⊔ Z := le_sup_left
  have hZle : Z ≤ H ⊔ Z := le_sup_right
  -- `Z` sits in the centre of `↥(H ⊔ Z)`, whence is normal there
  have hZcenter : Z.subgroupOf (H ⊔ Z) ≤ Subgroup.center ↥(H ⊔ Z) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hzX : (z : X) ∈ Z := Subgroup.mem_subgroupOf.mp hz
    have hcomm := Subgroup.mem_centralizer_iff.mp (hZ hzX) (w : X) w.property
    simpa using hcomm
  have hZnormal : (Z.subgroupOf (H ⊔ Z)).Normal := Subgroup.normal_of_le_center hZcenter
  have hx' : (⟨x, hx⟩ : ↥(H ⊔ Z)) ∈ H.subgroupOf (H ⊔ Z) ⊔ Z.subgroupOf (H ⊔ Z) := by
    rw [← Subgroup.subgroupOf_sup hHle hZle, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨h, hh, z, hz, hhz⟩ :=
    (@Subgroup.mem_sup_of_normal_right ↥(H ⊔ Z) _ (H.subgroupOf (H ⊔ Z))
      (Z.subgroupOf (H ⊔ Z)) hZnormal (⟨x, hx⟩ : ↥(H ⊔ Z))).mp hx'
  exact ⟨h.1, Subgroup.mem_subgroupOf.mp hh, z.1, Subgroup.mem_subgroupOf.mp hz,
    by simpa using congrArg Subtype.val hhz⟩

/-- If `E ≤ E'` are perfect subgroups of a finite group `X` whose central quotients have the same
order, then `E = E'`. -/
private lemma eq_of_le_of_card_quotient_center_eq {X : Type*} [Group X] [Finite X]
    {E E' : Subgroup X} (hEE' : E ≤ E') (hperf : ⁅E, E⁆ = E) (hperf' : ⁅E', E'⁆ = E')
    (hcard : Nat.card (↥E ⧸ Subgroup.center ↥E) = Nat.card (↥E' ⧸ Subgroup.center ↥E')) :
    E = E' := by
  classical
  -- ## Step 1: `E' = E ⊔ Z`, where `Z` is the centre of `E'` inside `X`
  set Z : Subgroup X := (Subgroup.center ↥E').map E'.subtype with hZ
  have hZle : Z ≤ E' := Subgroup.map_subtype_le _
  set φ : ↥E →* (↥E' ⧸ Subgroup.center ↥E') :=
    (QuotientGroup.mk' (Subgroup.center ↥E')).comp (Subgroup.inclusion hEE') with hφ
  have hφ_apply : ∀ x : ↥E, φ x = QuotientGroup.mk (Subgroup.inclusion hEE' x) := fun _ => rfl
  -- the kernel of `φ` lies in the centre of `E`
  have hker_le : φ.ker ≤ Subgroup.center ↥E := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxmem : Subgroup.inclusion hEE' x ∈ Subgroup.center ↥E' := by
      have h1 : φ x = 1 := by
        rw [MonoidHom.mem_ker] at hx
        exact hx
      rw [hφ_apply] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hcomm := Subgroup.mem_center_iff.mp hxmem (Subgroup.inclusion hEE' y)
    apply Subtype.ext
    simpa using congrArg Subtype.val hcomm
  have hker_card : Nat.card ↥φ.ker ≤ Nat.card ↥(Subgroup.center ↥E) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hker_le)
  have hEcard : Nat.card ↥E
      = Nat.card (↥E ⧸ Subgroup.center ↥E) * Nat.card ↥(Subgroup.center ↥E) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  -- hence `φ` is onto
  have hrange_ge : Nat.card (↥E' ⧸ Subgroup.center ↥E') ≤ Nat.card ↥φ.range := by
    have h1 : Nat.card ↥φ.ker * Nat.card ↥φ.range = Nat.card ↥E :=
      Subgroup.card_ker_mul_card_range φ
    have hkpos : 0 < Nat.card ↥φ.ker := Nat.card_pos
    have hineq : Nat.card (↥E' ⧸ Subgroup.center ↥E') * Nat.card ↥φ.ker
        ≤ Nat.card ↥φ.range * Nat.card ↥φ.ker := by
      rw [mul_comm (Nat.card ↥φ.range), h1, hEcard, hcard]
      exact Nat.mul_le_mul_left _ hker_card
    exact Nat.le_of_mul_le_mul_right hineq hkpos
  have hrange_top : φ.range = ⊤ := by
    refine Subgroup.eq_of_le_of_card_ge le_top ?_
    rw [Subgroup.card_top]
    exact hrange_ge
  have hsurj : Function.Surjective φ := fun y => by
    have hy : y ∈ φ.range := by rw [hrange_top]; exact Subgroup.mem_top y
    rwa [MonoidHom.mem_range] at hy
  -- so `E' = E Z`
  have hE'le : E' ≤ E ⊔ Z := by
    intro g hg
    obtain ⟨e, he⟩ := hsurj (QuotientGroup.mk (⟨g, hg⟩ : ↥E'))
    have hker' : (Subgroup.inclusion hEE' e)⁻¹ * (⟨g, hg⟩ : ↥E') ∈ Subgroup.center ↥E' := by
      rw [hφ_apply] at he
      exact QuotientGroup.eq.mp he
    have hgz : (⟨g, hg⟩ : ↥E')
        = Subgroup.inclusion hEE' e * ((Subgroup.inclusion hEE' e)⁻¹ * (⟨g, hg⟩ : ↥E')) := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    have hval : g = e.1 * ((Subgroup.inclusion hEE' e)⁻¹ * (⟨g, hg⟩ : ↥E')).1 :=
      congrArg Subtype.val hgz
    rw [hval]
    exact Subgroup.mul_mem_sup e.2 (Subgroup.mem_map.mpr ⟨_, hker', rfl⟩)
  have hsup : E ⊔ Z = E' := le_antisymm (sup_le hEE' hZle) hE'le
  -- ## Step 2: `Z` is central in `E'`, so `⁅E',E'⁆ = ⁅E,E⁆`
  have hZcentral : Z ≤ Subgroup.centralizer ((E ⊔ Z : Subgroup X) : Set X) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    rintro w hw
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
    have hcomm := congrArg Subtype.val (Subgroup.mem_center_iff.mp hu (⟨w, hsup ▸ hw⟩ : ↥E'))
    simpa using hcomm
  have hcomm_le : ⁅E', E'⁆ ≤ ⁅E, E⁆ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨e₁, he₁, z₁, hz₁, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer hZcentral (hsup ▸ hx)
    obtain ⟨e₂, he₂, z₂, hz₂, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer hZcentral (hsup ▸ hy)
    have hz₁e₂ : Commute z₁ e₂ := by
      have h := Subgroup.mem_centralizer_iff.mp (hZcentral hz₁)
      exact (h e₂ (hsup ▸ hEE' he₂)).symm
    have hz₁z₂ : Commute z₁ z₂ := by
      have h := Subgroup.mem_centralizer_iff.mp (hZcentral hz₁)
      exact (h z₂ (hsup ▸ hZle hz₂)).symm
    have hz₂e₁ : Commute z₂ e₁ := by
      have h := Subgroup.mem_centralizer_iff.mp (hZcentral hz₂)
      exact (h e₁ (hsup ▸ hEE' he₁)).symm
    have hid : ⁅e₁ * z₁, e₂ * z₂⁆ = ⁅e₁, e₂⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, (hz₁e₂.mul_right hz₁z₂).commutator_eq,
        commutatorElement_mul_right_eq_mul_conj, hz₂e₁.symm.commutator_eq]
      group
    rw [hid]
    exact Subgroup.commutator_mem_commutator he₁ he₂
  have hE'le' : E' ≤ E := by
    calc E' = ⁅E', E'⁆ := hperf'.symm
      _ ≤ ⁅E, E⁆ := hcomm_le
      _ = E := hperf
  exact le_antisymm hEE' hE'le'

/-- **Uniqueness of the quasisimple subgroup with central quotient `A₇`.** If `E ≤ E'` are
quasisimple subgroups of a finite group `X` and `E/Z(E) ≅ A₇ ≅ E'/Z(E')`, then `E = E'`.
No normality of `E` or `E'` in `X` is needed. -/
theorem EqOfQuasisimpleOfA7QuotientNoNormal {X : Type*} [Group X] [Finite X]
    {E E' : Subgroup X} (hEE' : E ≤ E')
    (hEq : Work.GW2.IsQuasisimple E) (hEq' : Work.GW2.IsQuasisimple E')
    (hA7E : Nonempty ((↥E ⧸ Subgroup.center ↥E) ≃* alternatingGroup (Fin 7)))
    (hA7E' : Nonempty ((↥E' ⧸ Subgroup.center ↥E') ≃* alternatingGroup (Fin 7))) : E = E' := by
  refine eq_of_le_of_card_quotient_center_eq hEE' hEq.1 hEq'.1 ?_
  obtain ⟨e₁⟩ := hA7E
  obtain ⟨e₂⟩ := hA7E'
  exact (Nat.card_congr e₁.toEquiv).trans (Nat.card_congr e₂.toEquiv).symm

end Work.CORE3.MData
