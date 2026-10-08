import Mathlib
import Submission.Work.ThreePoints.Omega

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.ThreePoints.ThmC

/-- If `x` lies in a subgroup `P` and `x²` centralises `P`, then `x` centralises `P`: the quotient
`P/Z(P)` (the group of inner automorphisms of `P`) has odd order when `P` has odd order, so an
element whose square is central must be central. -/
theorem mem_centralizer_of_sq_mem_centralizer {G : Type} [Group G] {P : Subgroup G} {x : G}
    (hodd : Odd (Nat.card ↥P)) (hx : x ∈ P)
    (hx2 : x * x ∈ Subgroup.centralizer (P : Set G)) :
    x ∈ Subgroup.centralizer (P : Set G) := by
  classical
  set Z : Subgroup ↥P := Subgroup.center ↥P with hZdef
  haveI : Z.Normal := inferInstance
  have hZmem : (⟨x ^ 2, by rw [pow_two]; exact P.mul_mem hx hx⟩ : ↥P) ∈ Z := by
    rw [hZdef, Subgroup.mem_center_iff]
    intro y
    have h1 : (y : G) * (x * x) = (x * x) * (y : G) :=
      (Subgroup.mem_centralizer_iff.mp hx2) (y : G) y.2
    exact Subtype.ext (by simpa [pow_two] using h1)
  have hcardZ : Nat.card (↥P ⧸ Z) ∣ Nat.card ↥P := by
    have h := Subgroup.card_mul_index Z
    rw [Subgroup.index_eq_card] at h
    exact ⟨Nat.card ↥Z, by rw [← h, mul_comm]⟩
  have hoddQ : Odd (Nat.card (↥P ⧸ Z)) := Work.ThreePoints.Odd.of_dvd hcardZ hodd
  have h2 : orderOf (QuotientGroup.mk' Z (⟨x, hx⟩ : ↥P)) ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    simpa using hZmem
  have hdiv : orderOf (QuotientGroup.mk' Z (⟨x, hx⟩ : ↥P)) ∣ Nat.card (↥P ⧸ Z) :=
    orderOf_dvd_natCard _
  have h1 : orderOf (QuotientGroup.mk' Z (⟨x, hx⟩ : ↥P)) ∣ 1 := by
    have h := Nat.dvd_gcd h2 hdiv
    rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hoddQ)] at h
  have hone : QuotientGroup.mk' Z (⟨x, hx⟩ : ↥P) = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.dvd_one.mp h1
  have hxZ : (⟨x, hx⟩ : ↥P) ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
    exact hone
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h := (Subgroup.mem_center_iff.mp hxZ) (⟨y, hy⟩ : ↥P)
  have h' := Subtype.ext_iff.mp h
  simpa using h'

end Work.ThreePoints.ThmC
