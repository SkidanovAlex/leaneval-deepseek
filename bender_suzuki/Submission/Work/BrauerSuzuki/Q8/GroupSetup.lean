import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic
import Submission.Work.BrauerSuzuki.Group.odd_orderOf_mul
import Submission.Work.BrauerSuzuki.Group.isConj_of_orderOf_eq_two
import Submission.Work.BrauerSuzuki.Sylow.genQuaternion_sylow_quotient
import Submission.Work.BrauerSuzuki.OddCore.le_of_normal_odd
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Group-theoretic prerequisites for Glauberman's `Q₈` case

If `S` is a Sylow `2`-subgroup of a finite group `G` equipped with the Dade normal form
`d : GenQuaternionData ↥S` of a generalized quaternion group, then `↥S` has a unique
involution (`Work.BrauerSuzuki.Quaternion.genQuaternionData_basic`), and by Sylow conjugacy
so does every Sylow `2`-subgroup of `G`.  Consequently (Glauberman 1974; Gorenstein 12.1.7)

* all involutions of `G` are conjugate, and
* the product of two involutions of `G` has odd order,

and if in addition `|Z(G)| = 2`, then `G` has a *unique* involution (which is then central):
`|Z(G)| = 2` makes the centre an ordinary group of order `2`, whose unique involution is
central, and two distinct commuting involutions would generate a Klein four-group, which
cannot sit inside a Sylow `2`-subgroup isomorphic to a generalized quaternion group.
-/

set_option autoImplicit false

open Classical
open scoped Pointwise

namespace Work.BrauerSuzuki.Q8

variable {G : Type*} [Group G]

/-- In Dade's normal form `P = ⟨τ, ρ⟩` of a generalized quaternion group, `τ ^ (2 ^ (n-1))`
is the unique involution of `P` (Dade 6.2). -/
theorem hasUniqueInvolution_of_genQuaternionData {P : Type*} [Group P] [Finite P]
    (d : Work.BrauerSuzuki.GenQuaternionData P) : Work.BrauerSuzuki.HasUniqueInvolution P := by
  obtain ⟨-, -, hord, huniq, -⟩ := Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d
  exact ⟨d.tau ^ (2 ^ (d.n - 1)), hord, huniq⟩

/-- `HasUniqueInvolution` is preserved by a group isomorphism. -/
theorem hasUniqueInvolution_of_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    (h : Work.BrauerSuzuki.HasUniqueInvolution P) : Work.BrauerSuzuki.HasUniqueInvolution Q := by
  obtain ⟨z, hz2, hzu⟩ := h
  refine ⟨e z, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]; exact hz2
  · intro w hw
    have h1 : orderOf (e.symm w) = 2 := by
      rw [← MulEquiv.orderOf_eq e (e.symm w), MulEquiv.apply_symm_apply, hw]
    have h2 : e (e.symm w) = e z := by rw [hzu (e.symm w) h1]
    rwa [MulEquiv.apply_symm_apply] at h2

/-- Every Sylow `2`-subgroup of a finite group with a generalized quaternion Sylow `2`-subgroup
has a unique involution: Sylow subgroups are conjugate and `↥S ≅ Q₈` has a unique involution. -/
theorem hasUniqueInvolution_sylow_of_genQuaternionData {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    ∀ T : Sylow 2 G, Work.BrauerSuzuki.HasUniqueInvolution ↥T := by
  haveI : Nonempty (Sylow 2 G) := ⟨S⟩
  intro T
  obtain ⟨c, hc⟩ := (Sylow.isPretransitive_of_finite (p := 2) (G := G)).exists_smul_eq S T
  have hsub : (MulAut.conj c) • (S : Subgroup G) = (T : Subgroup G) := by
    rw [← Sylow.pointwise_smul_def (g := MulAut.conj c) (P := S), ← Sylow.smul_def, hc]
  have hmap : (S : Subgroup G).map (MulAut.conj c).toMonoidHom = (T : Subgroup G) := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxy⟩
      have h1 : (MulAut.conj c) • x ∈ (T : Subgroup G) := by
        have h2 : (MulAut.conj c) • x ∈ (MulAut.conj c) • (S : Subgroup G) :=
          Subgroup.smul_mem_pointwise_smul x (MulAut.conj c) (S : Subgroup G) hx
        rwa [hsub] at h2
      rw [MulAut.smul_def] at h1
      rw [← hxy]
      exact h1
    · intro hy
      have h1 : y ∈ (MulAut.conj c) • (S : Subgroup G) := by rw [hsub]; exact hy
      obtain ⟨x, hx, hxy⟩ :=
        (Subgroup.mem_smul_pointwise_iff_exists y (MulAut.conj c) (S : Subgroup G)).mp h1
      rw [MulAut.smul_def] at hxy
      exact ⟨x, hx, hxy⟩
  refine hasUniqueInvolution_of_mulEquiv
    ((Subgroup.equivMapOfInjective (S : Subgroup G) (MulAut.conj c).toMonoidHom
        (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr hmap))
    (hasUniqueInvolution_of_genQuaternionData d)

/-- Glauberman (1974), step (3)(d) input: in a finite group with a quaternion Sylow
`2`-subgroup, all involutions are conjugate (Gorenstein 12.1.7). -/
theorem isConj_involutions_of_genQuaternionData {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) {u v : G}
    (hu : orderOf u = 2) (hv : orderOf v = 2) : IsConj u v :=
  Work.BrauerSuzuki.Group.isConj_of_orderOf_eq_two
    (hasUniqueInvolution_sylow_of_genQuaternionData S d) hu hv

/-- Glauberman (1974), step (3)(d) input: in a finite group with a quaternion Sylow
`2`-subgroup, the product of two involutions has odd order (Gorenstein 12.1.7). -/
theorem odd_orderOf_mul_of_genQuaternionData {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) {u v : G}
    (hu : orderOf u = 2) (hv : orderOf v = 2) : Odd (orderOf (u * v)) :=
  Work.BrauerSuzuki.Group.odd_orderOf_mul
    (hasUniqueInvolution_sylow_of_genQuaternionData S d) hu hv

/-- If `|Z(G)| = 2` and every Sylow `2`-subgroup of `G` has a unique involution, then `G` has
a unique involution: the centre is a group of order `2`, its non-identity element `z` is an
involution, and any other involution `u` commutes with `z` and would generate a Klein
four-group with it, contradicting `eq_of_commute_of_unique_sylow`. -/
theorem unique_involution_of_card_center_eq_two {G : Type*} [Group G] [Finite G]
    (h : ∀ T : Sylow 2 G, Work.BrauerSuzuki.HasUniqueInvolution ↥T)
    (hZ : Nat.card ↥(Subgroup.center G) = 2) :
    ∀ u v : G, orderOf u = 2 → orderOf v = 2 → u = v := by
  letI : Fintype ↥(Subgroup.center G) := Fintype.ofFinite _
  -- a non-identity element of the centre
  have hcard : Fintype.card ↥(Subgroup.center G) = 2 := by
    rw [← Nat.card_eq_fintype_card]; exact hZ
  obtain ⟨z, hz⟩ : ∃ z : ↥(Subgroup.center G), z ≠ 1 := by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card
      (by rw [hcard]; norm_num : 1 < Fintype.card ↥(Subgroup.center G))
    rcases eq_or_ne a 1 with h | h
    · exact ⟨b, fun hb => hab (by rw [h, hb])⟩
    · exact ⟨a, h⟩
  have hz2 : orderOf z = 2 := by
    have hdvd : orderOf z ∣ 2 := by
      rw [← hZ]; exact orderOf_dvd_natCard z
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h1
    · exact absurd h1 (fun h1 => hz (orderOf_eq_one_iff.mp h1))
    · exact h1
  intro u v hu hv
  have hzu : (z : G) = u :=
    Work.BrauerSuzuki.Group.eq_of_commute_of_unique_sylow h
      (by rw [Subgroup.orderOf_coe, hz2]) hu ((Subgroup.mem_center_iff.mp z.2) u).symm
  have hzv : (z : G) = v :=
    Work.BrauerSuzuki.Group.eq_of_commute_of_unique_sylow h
      (by rw [Subgroup.orderOf_coe, hz2]) hv ((Subgroup.mem_center_iff.mp z.2) v).symm
  rw [← hzu, ← hzv]

end Work.BrauerSuzuki.Q8
