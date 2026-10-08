/-
# The `D = A` branch of the `C₄` squaring dichotomy

If no `x ∈ C ∖ A` has `x² ∈ A²`, then the squaring map `x ↦ x²`, followed by reduction mod `A²`,
is injective on the cosets of `A`: the induced map `C/A → A/A²` is injective, so
`|C/A| ≤ |A/A²|`, and hence `|C| ≤ |A| · |A/A²| = |A| · |Ω₁(P)|` (as `A² = Ω₁(P)`).
-/
import Mathlib
import Submission.Work.Higman.C4Cover.c4_cover_card_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman.C4Cover

variable {P : Type} [Group P] [Finite P]

/-- **The `D = A` branch.**  In the `C₄` setting, if the only `x ∈ C` with `x² ∈ A²` lie in `A`,
then `|C| ≤ |A| · |Ω₁(P)|`. -/
theorem c4_cover_card_le_of_ker (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hAC : A ≤ C)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hk : ∀ x ∈ C, x ^ 2 ∈ Work.Higman.powSub A 2 → x ∈ A) :
    Nat.card ↥C ≤ Nat.card ↥(Work.Higman.omega1 P) * Nat.card ↥A := by
  classical
  have hAn : A.Normal := hGs ▸ Subgroup.commutator_normal (⊤ : Subgroup P) ⊤
  have hZ2n : (Work.Higman.powSub A 2).Normal := Work.Higman.powSub_normal hAn 2
  have hZ2c : Work.Higman.powSub A 2 ≤ Subgroup.center P := htop ▸ h.omega1_le_center
  have hZ2le : Work.Higman.powSub A 2 ≤ A := Work.Higman.powSub_le (by norm_num)
  haveI : (A.subgroupOf C).Normal := hAn.subgroupOf C
  haveI : ((Work.Higman.powSub A 2).subgroupOf A).Normal := hZ2n.subgroupOf A
  -- centrality of `A²`-elements: `t * w = w * t`
  have hcen : ∀ {w : P}, w ∈ Work.Higman.powSub A 2 → ∀ t : P, t * w = w * t :=
    fun {w} hw t => Subgroup.mem_center_iff.mp (hZ2c hw) t
  have hcomm_mem : ∀ x : ↥C, ∀ z ∈ A, ⁅z, (x : P)⁆ ∈ Work.Higman.powSub A 2 := by
    intro x z hz
    have h1 : ⁅z, (x : P)⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator (hAC hz) x.2
    rwa [hCd] at h1
  -- the key identity
  have hkey : ∀ x : ↥C, ∀ z : P, ⁅z, (x : P)⁆ ∈ Work.Higman.powSub A 2 →
      (((x : P) * z) ^ 2)⁻¹ * ((x : P)) ^ 2 = (⁅z, (x : P)⁆ * z ^ 2)⁻¹ := by
    intro x z hc
    have h1 : ((x : P) * z) ^ 2 = ⁅z, (x : P)⁆ * ((x : P)) ^ 2 * z ^ 2 :=
      sq_mul_of_commutator_comm (hcen hc (x : P))
    have hcx : ⁅z, (x : P)⁆ * ((x : P)) ^ 2 = ((x : P)) ^ 2 * ⁅z, (x : P)⁆ :=
      (hcen hc ((x : P) ^ 2)).symm
    have hcx' : (⁅z, (x : P)⁆)⁻¹ * ((x : P)) ^ 2
        = ((x : P)) ^ 2 * (⁅z, (x : P)⁆)⁻¹ := by
      calc (⁅z, (x : P)⁆)⁻¹ * ((x : P)) ^ 2
          = (⁅z, (x : P)⁆)⁻¹ * ((x : P)) ^ 2 * ⁅z, (x : P)⁆ * (⁅z, (x : P)⁆)⁻¹ := by
            group
        _ = (⁅z, (x : P)⁆)⁻¹ * (((x : P)) ^ 2 * ⁅z, (x : P)⁆) * (⁅z, (x : P)⁆)⁻¹ := by
            group
        _ = (⁅z, (x : P)⁆)⁻¹ * (⁅z, (x : P)⁆ * ((x : P)) ^ 2) * (⁅z, (x : P)⁆)⁻¹ := by
            rw [← hcx]
        _ = ((x : P)) ^ 2 * (⁅z, (x : P)⁆)⁻¹ := by group
    rw [h1, mul_inv_rev, mul_inv_rev, mul_inv_rev]
    rw [show (z ^ 2)⁻¹ * ((((x : P)) ^ 2)⁻¹ * (⁅z, (x : P)⁆)⁻¹) * ((x : P)) ^ 2
        = (z ^ 2)⁻¹ * ((((x : P)) ^ 2)⁻¹ * ((⁅z, (x : P)⁆)⁻¹ * ((x : P)) ^ 2)) by group]
    rw [hcx']
    group
  -- the induced map on cosets
  have hwd : ∀ x y : ↥C, QuotientGroup.leftRel (A.subgroupOf C) x y →
      (QuotientGroup.mk ((⟨(x : P) ^ 2, hsq (x : P)⟩ : ↥A)) :
        ↥A ⧸ ((Work.Higman.powSub A 2).subgroupOf A))
        = (QuotientGroup.mk ((⟨(y : P) ^ 2, hsq (y : P)⟩ : ↥A)) :
          ↥A ⧸ ((Work.Higman.powSub A 2).subgroupOf A)) := by
    intro x y hxy
    set z : P := (x : P)⁻¹ * (y : P) with hzdef
    have hzA : z ∈ A := by
      have h1 : ((x⁻¹ * y : ↥C) : P) ∈ A :=
        Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hxy)
      rw [hzdef]; simpa using h1
    have hc := hcomm_mem x z hzA
    have hz2 : z ^ 2 ∈ Work.Higman.powSub A 2 := Work.Higman.pow_mem_powSub (n := 2) hzA
    have hyx : (y : P) = (x : P) * z := by rw [hzdef]; group
    rw [QuotientGroup.eq]
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    have hk' : (((x : P) * z) ^ 2)⁻¹ * ((x : P)) ^ 2 = (⁅z, (x : P)⁆ * z ^ 2)⁻¹ :=
      hkey x z hc
    have h2 : (((x : P)) ^ 2)⁻¹ * ((y : P)) ^ 2 = ⁅z, (x : P)⁆ * z ^ 2 := by
      rw [hyx]
      calc (((x : P)) ^ 2)⁻¹ * ((x : P) * z) ^ 2
          = ((((x : P) * z) ^ 2)⁻¹ * ((x : P)) ^ 2)⁻¹ := by group
        _ = ((⁅z, (x : P)⁆ * z ^ 2)⁻¹)⁻¹ := by rw [hk']
        _ = ⁅z, (x : P)⁆ * z ^ 2 := by rw [inv_inv]
    rw [h2]
    exact (Work.Higman.powSub A 2).mul_mem hc hz2
  let f : (↥C ⧸ (A.subgroupOf C)) → (↥A ⧸ ((Work.Higman.powSub A 2).subgroupOf A)) :=
    Quotient.lift (fun x : ↥C => (QuotientGroup.mk (⟨(x : P) ^ 2, hsq (x : P)⟩ : ↥A) :
      ↥A ⧸ ((Work.Higman.powSub A 2).subgroupOf A))) hwd
  have hfinj : Function.Injective f := by
    intro p q
    refine Quotient.inductionOn p (fun x => ?_)
    refine Quotient.inductionOn q (fun y => ?_)
    intro hpq
    change (QuotientGroup.mk ((⟨(x : P) ^ 2, hsq (x : P)⟩ : ↥A)) :
        ↥A ⧸ ((Work.Higman.powSub A 2).subgroupOf A))
      = (QuotientGroup.mk ((⟨(y : P) ^ 2, hsq (y : P)⟩ : ↥A)) :
        ↥A ⧸ ((Work.Higman.powSub A 2).subgroupOf A)) at hpq
    rw [QuotientGroup.eq] at hpq
    rw [Subgroup.mem_subgroupOf] at hpq
    have hpq' : (((x : P)) ^ 2)⁻¹ * ((y : P)) ^ 2 ∈ Work.Higman.powSub A 2 := hpq
    set z : P := (x : P)⁻¹ * (y : P) with hzdef
    have hzC : z ∈ C := by
      rw [hzdef]; exact C.mul_mem (C.inv_mem x.2) y.2
    have hcz : ⁅z, (x : P)⁆ ∈ Work.Higman.powSub A 2 := by
      have h1 : ⁅z, (x : P)⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hzC x.2
      rwa [hCd] at h1
    have hyx : (y : P) = (x : P) * z := by rw [hzdef]; group
    -- `(⁅z,x⁆ z²)⁻¹ = (y²)⁻¹ x²`
    have hkeyz : (((x : P) * z) ^ 2)⁻¹ * ((x : P)) ^ 2 = (⁅z, (x : P)⁆ * z ^ 2)⁻¹ :=
      hkey x z hcz
    have hwmem : ⁅z, (x : P)⁆ * z ^ 2 ∈ Work.Higman.powSub A 2 := by
      have h1 : (⁅z, (x : P)⁆ * z ^ 2)⁻¹ ∈ Work.Higman.powSub A 2 := by
        rw [← hkeyz]
        have h3 : (((x : P) * z) ^ 2)⁻¹ * ((x : P)) ^ 2
            = ((((x : P)) ^ 2)⁻¹ * ((x : P) * z) ^ 2)⁻¹ := by
          rw [mul_inv_rev, inv_inv]
        rw [h3, ← hyx]
        exact (Work.Higman.powSub A 2).inv_mem hpq'
      have h2 : ((⁅z, (x : P)⁆ * z ^ 2)⁻¹)⁻¹ ∈ Work.Higman.powSub A 2 :=
        (Work.Higman.powSub A 2).inv_mem h1
      simpa using h2
    have hz2 : z ^ 2 ∈ Work.Higman.powSub A 2 := by
      have h1 : (⁅z, (x : P)⁆)⁻¹ * (⁅z, (x : P)⁆ * z ^ 2) ∈ Work.Higman.powSub A 2 :=
        (Work.Higman.powSub A 2).mul_mem ((Work.Higman.powSub A 2).inv_mem hcz) hwmem
      have h2 : (⁅z, (x : P)⁆)⁻¹ * (⁅z, (x : P)⁆ * z ^ 2) = z ^ 2 := by group
      rwa [h2] at h1
    rw [QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    show (x : P)⁻¹ * (y : P) ∈ A
    exact hk z hzC hz2
  -- cardinalities
  have hcard_sub : Nat.card ↥(A.subgroupOf C) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv
  have hcard_Z : Nat.card ↥((Work.Higman.powSub A 2).subgroupOf A)
      = Nat.card ↥(Work.Higman.powSub A 2) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ2le).toEquiv
  have hdecomp : Nat.card ↥C = Nat.card (↥C ⧸ (A.subgroupOf C)) * Nat.card ↥A := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf C), hcard_sub]
  have hdecomp2 : Nat.card ↥A
      = Nat.card (↥A ⧸ ((Work.Higman.powSub A 2).subgroupOf A))
        * Nat.card ↥(Work.Higman.powSub A 2) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((Work.Higman.powSub A 2).subgroupOf A),
      hcard_Z]
  have hZ2card : Nat.card ↥(Work.Higman.powSub A 2) = Nat.card ↥(Work.Higman.omega1 P) := by
    rw [htop]
  have hquot : Nat.card (↥A ⧸ ((Work.Higman.powSub A 2).subgroupOf A))
      = Nat.card ↥(Work.Higman.omega1 P) := by
    have hpos : 0 < Nat.card ↥(Work.Higman.omega1 P) := Nat.card_pos
    have h3 : Nat.card (↥A ⧸ ((Work.Higman.powSub A 2).subgroupOf A))
        * Nat.card ↥(Work.Higman.powSub A 2) = Nat.card ↥A := hdecomp2.symm
    rw [hZ2card, hcard, pow_two] at h3
    exact Nat.eq_of_mul_eq_mul_right hpos h3
  calc Nat.card ↥C = Nat.card (↥C ⧸ (A.subgroupOf C)) * Nat.card ↥A := hdecomp
    _ ≤ Nat.card (↥A ⧸ ((Work.Higman.powSub A 2).subgroupOf A)) * Nat.card ↥A :=
        Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective f hfinj)
    _ = Nat.card ↥(Work.Higman.omega1 P) * Nat.card ↥A := by rw [hquot]

end Work.Higman.C4Cover
