/-
# `Work.NormalComplement.sec5f_setup`

The action of `𝒩 = N_G(V)` (with `V = centD H t`) on the set `Ω_V` of fixed points of `V` in
`Ω = G ⧸ H`, as a `MulAction` on the type `Sec5f.Omega H t`, together with the kernel `K` of this
action and the induced `MulAction` of `𝒩 ⧸ K` on `Ω_V`.

This is the setting in which Peterfalvi I Ch. III §5 Prop. 2 (a) applies Appendix III (2)–(5)
(see `Work.NormalComplement.AppIIIProp`).
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.ThreePoints.P3NeBot.p3_twoTransitive
import Submission.Work.ThreePoints.P3NeBot.maximal_of_twoTransitive
import Submission.Work.ThreePoints.P3Sub.Helpers

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 800000

open Classical
open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement
namespace Sec5f

open Submission.Blueprint

variable {G : Type} [Group G]

/-- `𝒩 = N_G(V)`, the normaliser of `V = centD H t`. -/
abbrev NN (H : Subgroup G) (t : G) : Subgroup G :=
  Subgroup.normalizer (Submission.Blueprint.centD H t : Set G)

/-- `Ω_V`, the set of fixed points of `V = centD H t` in `Ω = G ⧸ H`, as a type. -/
abbrev Omega (H : Subgroup G) (t : G) : Type _ :=
  ↥(Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t))

variable {H : Subgroup G} {t : G}

/-- `𝒩 = N_G(V)` preserves the set of fixed points of `V`. -/
theorem smul_mem_omega (g : G) (hg : g ∈ NN H t) {ω : G ⧸ H}
    (hω : ω ∈ Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t)) :
    g • ω ∈ Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t) :=
  Work.ThreePoints.P3NeBot.smul_mem_fixedPts_of_mem_normalizer hg hω

instance : SMul ↥(NN H t) (Omega H t) where
  smul g ω := ⟨(g : G) • (ω : G ⧸ H), smul_mem_omega (g : G) g.2 ω.2⟩

@[simp]
theorem coe_smul (g : ↥(NN H t)) (ω : Omega H t) :
    ((g • ω : Omega H t) : G ⧸ H) = (g : G) • (ω : G ⧸ H) := rfl

instance : MulAction ↥(NN H t) (Omega H t) where
  one_smul ω := Subtype.ext (by rw [coe_smul, OneMemClass.coe_one, one_smul])
  mul_smul g h ω := Subtype.ext (by rw [coe_smul, coe_smul, coe_smul, Subgroup.coe_mul, mul_smul])

/-- The kernel `K` of the action of `𝒩 = N_G(V)` on `Ω_V`. -/
noncomputable def KK (H : Subgroup G) (t : G) : Subgroup ↥(NN H t) :=
  (MulAction.toPermHom ↥(NN H t) (Omega H t)).ker

instance : (KK H t).Normal := MonoidHom.normal_ker _

/-- The induced action of `𝒩 ⧸ K` on `Ω_V`. -/
noncomputable instance : MulAction (↥(NN H t) ⧸ KK H t) (Omega H t) :=
  MulAction.compHom (Omega H t) <|
    QuotientGroup.lift (KK H t) (MulAction.toPermHom ↥(NN H t) (Omega H t)) (le_refl _)

/-- The quotient action specialises to the action of `𝒩`. -/
@[simp]
theorem quotient_smul_mk (g : ↥(NN H t)) (ω : Omega H t) :
    (QuotientGroup.mk' (KK H t) g) • ω = g • ω := rfl

variable [Finite G]

/-- The base point `H` of `Ω_V`. -/
noncomputable def ptV (H : Subgroup G) (t : G) : Omega H t :=
  ⟨(QuotientGroup.mk (1 : G) : G ⧸ H),
    Work.ThreePoints.pt_mem_fixedPts_of_le_centD le_rfl⟩

/-- The point `H^t` of `Ω_V`. -/
noncomputable def pttV (H : Subgroup G) (t : G) : Omega H t :=
  ⟨(QuotientGroup.mk t : G ⧸ H),
    Work.ThreePoints.mk_t_mem_fixedPts_of_le_centD le_rfl⟩

/-- The base point is fixed by `g` exactly when `g ∈ H`. -/
theorem smul_ptV_eq_iff (g : ↥(NN H t)) :
    g • ptV H t = ptV H t ↔ (g : G) ∈ H := by
  constructor
  · intro h
    have h3 : ((g • ptV H t : Omega H t) : G ⧸ H) = (QuotientGroup.mk (1 : G) : G ⧸ H) := by
      rw [h]
      rfl
    simp only [coe_smul, ptV, Work.ThreePoints.smul_mk] at h3
    have h4 : ((g : G) * 1)⁻¹ * 1 ∈ H := QuotientGroup.eq.mp h3
    simpa using H.inv_mem h4
  · intro hg
    refine Subtype.ext ?_
    simp only [coe_smul, ptV, Work.ThreePoints.smul_mk]
    exact QuotientGroup.eq.mpr (by simpa using H.inv_mem hg)

/-- The stabiliser of the base point in `𝒩` is `𝒩 ⊓ H`. -/
theorem stabilizer_ptV : MulAction.stabilizer ↥(NN H t) (ptV H t)
    = (NN H t ⊓ H).subgroupOf (NN H t) := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact Subgroup.mem_subgroupOf.mpr ⟨g.2, (smul_ptV_eq_iff g).mp h⟩
  · intro hgh
    exact (smul_ptV_eq_iff g).mpr (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hgh)).2

/-- The kernel `K` of the action fixes the base point. -/
theorem KK_le_subgroupOf : KK H t ≤ (NN H t ⊓ H).subgroupOf (NN H t) := by
  intro g hg
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  refine ⟨g.2, ?_⟩
  rw [← smul_ptV_eq_iff g]
  exact congrArg (fun e : Equiv.Perm (Omega H t) => e (ptV H t))
    (MonoidHom.mem_ker.mp hg)

/-- The stabiliser of the base point in `𝒩 ⧸ K` is the image of `𝒩 ⊓ H`. -/
theorem stabilizer_ptV_quot :
    MulAction.stabilizer (↥(NN H t) ⧸ KK H t) (ptV H t)
      = ((NN H t ⊓ H).subgroupOf (NN H t)).map (QuotientGroup.mk' (KK H t)) := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (KK H t) x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    rw [MulAction.mem_stabilizer_iff] at hx
    rw [quotient_smul_mk] at hx
    exact ⟨g, Subgroup.mem_subgroupOf.mpr ⟨g.2, (smul_ptV_eq_iff g).mp hx⟩, rfl⟩
  · rintro ⟨y, hy, hyg⟩
    rw [MulAction.mem_stabilizer_iff, ← hyg, quotient_smul_mk]
    exact (smul_ptV_eq_iff y).mpr (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).2

/-- The image of the kernel `K` in `G` lies in the two-point stabiliser `H ⊓ H^t`: every element of
`K` fixes both `H` and `H^t`. -/
theorem KK_map_le_twoPoint :
    (KK H t).map (NN H t).subtype ≤ Submission.Blueprint.twoPoint H t := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  have hker := MonoidHom.mem_ker.mp hg
  have hfixH : (g : G) ∈ H := (smul_ptV_eq_iff g).mp
    (congrArg (fun e : Equiv.Perm (Omega H t) => e (ptV H t)) hker)
  have hfixt : g • pttV H t = pttV H t :=
    congrArg (fun e : Equiv.Perm (Omega H t) => e (pttV H t)) hker
  have h2 : (g : G) • (QuotientGroup.mk t : G ⧸ H) = (QuotientGroup.mk t : G ⧸ H) := by
    have h3 : ((g • pttV H t : Omega H t) : G ⧸ H) = ((pttV H t : Omega H t) : G ⧸ H) := by
      rw [hfixt]
    simpa only [coe_smul, pttV] using h3
  rw [Work.ThreePoints.smul_mk] at h2
  have h3 : (((g : G) * t)⁻¹ * t)⁻¹ ∈ H := H.inv_mem (QuotientGroup.eq.mp h2)
  have h4 : t⁻¹ * (g : G) * t ∈ H := by
    have h5 : (((g : G) * t)⁻¹ * t)⁻¹ = t⁻¹ * (g : G) * t := by group
    rwa [h5] at h3
  rw [Submission.Blueprint.twoPoint, Subgroup.mem_inf]
  exact ⟨hfixH, Work.ThreePoints.mem_conj_iff.mpr h4⟩

/-- An element of `2`-power order in a finite group lies in every normal subgroup of odd index. -/
theorem mem_of_pow_two_eq_one_of_normal_odd_index {L : Type} [Group L] [Finite L]
    {N : Subgroup L} [hN : N.Normal] (hodd : Odd N.index) {x : L} {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : x ∈ N := by
  haveI := hN
  have h1 : orderOf (QuotientGroup.mk' N x) ∣ 2 ^ k := by
    rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, hx, map_one]
  have h2 : orderOf (QuotientGroup.mk' N x) ∣ N.index := by
    rw [Subgroup.index_eq_card]; exact orderOf_dvd_natCard _
  obtain ⟨j, -, hje⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h3 : 2 ^ j ∣ N.index := hje ▸ h2
  have hj0 : j = 0 := by
    by_contra hj
    obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have h2dvd : 2 ∣ N.index := by
      refine dvd_trans ?_ h3
      rw [ht, pow_succ]; exact dvd_mul_left 2 _
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
  have hone : orderOf (QuotientGroup.mk' N x) = 1 := by rw [hje, hj0, pow_zero]
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp hone)

/-- An element of `2`-power order in a finite group lies in every normal subgroup of odd index. -/
theorem mem_of_orderOf_eq_two_pow_of_normal_odd_index {L : Type} [Group L] [Finite L]
    {N : Subgroup L} [N.Normal] (hodd : Odd N.index) {x : L} {k : ℕ} (hx : orderOf x = 2 ^ k) :
    x ∈ N :=
  mem_of_pow_two_eq_one_of_normal_odd_index hodd (by rw [← hx, pow_orderOf_eq_one])

end Sec5f
end Work.NormalComplement
