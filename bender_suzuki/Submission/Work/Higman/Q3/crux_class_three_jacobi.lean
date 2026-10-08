import Mathlib
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.H8.Clean.Nsd
import Submission.Work.Higman.suzuki_unipotence

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman.Q3

/-!
## The class-three Jacobi identity in a Suzuki 2-group

Let `P` be a Suzuki 2-group, `A ⊴ P` a `ξ`-invariant abelian normal subgroup with
`A = ⁅P, P⁆` and `A ^ (2) = Ω₁(P)` (`powSub A 2 = omega1 P`).  We show

`⁅⁅x, y⁆, z⁆ * ⁅⁅y, z⁆, x⁆ * ⁅⁅z, x⁆, y⁆ = 1`.

The mathematical content is the following.  By Higman's elementary observation, every
involution of a Suzuki 2-group is central, so `Ω₁(P) ≤ Z(P)` (`IsSuzuki2Grp.omega1_le_center`);
thus `A ^ (2) ≤ Z(P)`.  Since `A = P'` is abelian, a double commutator `c = ⁅u, w⁆` with
`u ∈ A` satisfies `c ^ 2 = ⁅u ^ 2, w⁆` (as `u` commutes with `c`, both lying in the abelian
group `A`), and `u ^ 2 ∈ A ^ (2) ≤ Z(P)` gives `c ^ 2 = 1`; hence `c ∈ Ω₁(P) ≤ Z(P)`.  So
`γ₃(P) ≤ Z(P)` and `P` has nilpotency class at most three, whereupon the Hall–Witt identity
(or, in the form used here, Mathlib's
`commutatorElement_commutatorElement_conj_mul`) collapses to Jacobi.
-/

/-- If `P` is a Suzuki 2-group, `A = ⁅P, P⁆` is abelian and `A ^ (2) = Ω₁(P)`, then for
`u ∈ A` the commutator `⁅u, w⁆` is central. -/
theorem commutatorElement_mem_center_of_mem {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    {u : P} (hu : u ∈ A) (w : P) : ⁅u, w⁆ ∈ Subgroup.center P := by
  have hcA : ⁅u, w⁆ ∈ A := by
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top w)
    rwa [hGs] at h1
  -- `u` commutes with `⁅u, w⁆`, both being elements of the abelian group `A`
  have hcomm : Commute u ⁅u, w⁆ := hA.abelian u hu ⁅u, w⁆ hcA
  have h2 : ⁅u, w⁆ ^ 2 = ⁅u ^ 2, w⁆ := hcomm.commutatorElement_pow_left 2
  -- `u ^ 2` is a square of an element of `A`, hence lies in `A ^ (2) = Ω₁(P) ≤ Z(P)`
  have hu2 : u ^ 2 ∈ Work.Higman.omega1 P := by
    rw [← htop]
    exact Work.Higman.pow_mem_powSub hu
  have h3 : ⁅u ^ 2, w⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact ((Subgroup.mem_center_iff.mp (h.omega1_le_center hu2)) w).symm
  have hsq : ⁅u, w⁆ ^ 2 = 1 := by rw [h2, h3]
  exact h.omega1_le_center (Subgroup.subset_closure (Work.Higman.mem_sqOne.mpr hsq))

/-- If `A` is abelian and every `⁅u, w⁆` with `u ∈ A` is central, then for `u, v ∈ A` the
commutator depends only on the second factor: `⁅u, v * w⁆ = ⁅u, w⁆`. -/
theorem commutatorElement_mul_of_mem {P : Type} [Group P] {A : Subgroup P}
    (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hcen : ∀ u ∈ A, ∀ w : P, ⁅u, w⁆ ∈ Subgroup.center P)
    {u v : P} (hu : u ∈ A) (hv : v ∈ A) (w : P) : ⁅u, v * w⁆ = ⁅u, w⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have huv : ⁅u, v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hAb u hu v hv)
  rw [huv, one_mul]
  have hv' : v * ⁅u, w⁆ = ⁅u, w⁆ * v := (Subgroup.mem_center_iff.mp (hcen u hu w)) v
  rw [hv']
  group

theorem crux_class_three_jacobi {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A) (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P) (x y z : P) :
    ((x * y * x⁻¹ * y⁻¹) * z * (x * y * x⁻¹ * y⁻¹)⁻¹ * z⁻¹)
      * ((y * z * y⁻¹ * z⁻¹) * x * (y * z * y⁻¹ * z⁻¹)⁻¹ * x⁻¹)
      * ((z * x * z⁻¹ * x⁻¹) * y * (z * x * z⁻¹ * x⁻¹)⁻¹ * y⁻¹) = 1 := by
  show ⁅⁅x, y⁆, z⁆ * ⁅⁅y, z⁆, x⁆ * ⁅⁅z, x⁆, y⁆ = 1
  -- every commutator of elements of `P` lies in `A = ⁅P, P⁆`
  have hmemA : ∀ u v : P, ⁅u, v⁆ ∈ A := by
    intro u v
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v)
    rwa [hGs] at h1
  have hcen : ∀ u ∈ A, ∀ w : P, ⁅u, w⁆ ∈ Subgroup.center P :=
    fun u hu w => commutatorElement_mem_center_of_mem h hA hGs htop hu w
  have hmul : ∀ u ∈ A, ∀ v ∈ A, ∀ w : P, ⁅u, v * w⁆ = ⁅u, w⁆ :=
    fun u hu v hv w => commutatorElement_mul_of_mem hA.abelian hcen hu hv w
  have hconj : ∀ p q : P, ⁅p, q⁆ * q = p * q * p⁻¹ := by
    intro p q
    rw [← conj_eq_commutatorElement_mul, MulAut.conj_apply]
  have h1 : ⁅⁅x, y⁆, y * z * y⁻¹⁆ = ⁅⁅x, y⁆, z⁆ := by
    rw [← hconj y z]
    exact hmul ⁅x, y⁆ (hmemA x y) ⁅y, z⁆ (hmemA y z) z
  have h2 : ⁅⁅y, z⁆, z * x * z⁻¹⁆ = ⁅⁅y, z⁆, x⁆ := by
    rw [← hconj z x]
    exact hmul ⁅y, z⁆ (hmemA y z) ⁅z, x⁆ (hmemA z x) x
  have h3 : ⁅⁅z, x⁆, x * y * x⁻¹⁆ = ⁅⁅z, x⁆, y⁆ := by
    rw [← hconj x y]
    exact hmul ⁅z, x⁆ (hmemA z x) ⁅x, y⁆ (hmemA x y) y
  have hw := commutatorElement_commutatorElement_conj_mul x y z
  rwa [h1, h2, h3] at hw

end Work.Higman.Q3
