/-
# `Submission.Work.NormalComplement.S5K.prop1_step3_defs`

Vocabulary for the proof of Peterfalvi I Ch. III §4 Prop. 1, step 3 (p.180): the action of
`𝒢 = N_G(P)` on the set `Ω_P = fixedPts H P` of fixed points of `P` in `Ω = G ⧸ H` (a point of `Ω`
is a coset `gH`, i.e. a conjugate `H^g`; it is fixed by `P` iff `P ≤ H^g`), the kernel `KKP` of this
action, the induced action of `𝒢 ⧸ KKP` on `Ω_P`, the base points `H` and `H^t`, and the elementary
API for these objects (stabilisers, kernel contained in the two-point stabiliser `D = H ⊓ H^t`).

`KKP` is the analogue for `P` of `Sec5Fix.P2a`'s `KK` (which is the kernel of the action of
`N_G(V)` on the fixed points of `V = centD H t`); the file is `sorry`-free and is the interface for
the leaf lemmas of the development.
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.P3Sub.Helpers
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
open Classical
open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement.S5K

variable {G : Type} [Group G] [Finite G]

/-- `𝒢 = N_G(P)`, the normaliser of the subgroup `P`. -/
abbrev NGP (P : Subgroup G) : Subgroup G := Subgroup.normalizer (P : Set G)

/-- `Ω_P`, the set of fixed points of `P` in `Ω = G ⧸ H`, as a type. -/
abbrev OmP (H P : Subgroup G) : Type _ := ↥(Submission.Blueprint.fixedPts H P)

/-- `N_G(P)` preserves the set of fixed points of `P`. -/
theorem smul_mem_OmP {H P : Subgroup G} {g : G} (hg : g ∈ NGP P) {ω : G ⧸ H}
    (hω : ω ∈ Submission.Blueprint.fixedPts H P) : g • ω ∈ Submission.Blueprint.fixedPts H P := by
  rw [Work.ThreePoints.mem_fixedPts] at hω ⊢
  intro x hx
  have hconj : g⁻¹ * x * g ∈ P :=
    ((Subgroup.mem_normalizer_iff''.mp hg) x).mp hx
  calc x • (g • ω) = (x * g) • ω := (mul_smul x g ω).symm
    _ = (g * (g⁻¹ * x * g)) • ω := by rw [show x * g = g * (g⁻¹ * x * g) from by group]
    _ = g • ((g⁻¹ * x * g) • ω) := mul_smul g _ ω
    _ = g • ω := by rw [hω _ hconj]

instance instSMulOmP {H P : Subgroup G} : SMul ↥(NGP P) (OmP H P) where
  smul g ω := ⟨(g : G) • (ω : G ⧸ H), smul_mem_OmP g.2 ω.2⟩

@[simp] theorem coe_smul_OmP {H P : Subgroup G} (g : ↥(NGP P)) (ω : OmP H P) :
    ((g • ω : OmP H P) : G ⧸ H) = (g : G) • (ω : G ⧸ H) := rfl

instance instMulActionOmP {H P : Subgroup G} : MulAction ↥(NGP P) (OmP H P) where
  one_smul ω := Subtype.ext (by rw [coe_smul_OmP, OneMemClass.coe_one, one_smul])
  mul_smul g h ω :=
    Subtype.ext (by rw [coe_smul_OmP, coe_smul_OmP, coe_smul_OmP, Subgroup.coe_mul, mul_smul])

/-- The kernel of the action of `𝒢 = N_G(P)` on `Ω_P`. -/
noncomputable def KKP (H P : Subgroup G) : Subgroup ↥(NGP P) :=
  (MulAction.toPermHom ↥(NGP P) (OmP H P)).ker

instance instKKPNormal (H P : Subgroup G) : (KKP H P).Normal := MonoidHom.normal_ker _

/-- The induced action of `𝒢 ⧸ KKP` on `Ω_P`. -/
noncomputable instance instMulActionQuotOmP (H P : Subgroup G) :
    MulAction (↥(NGP P) ⧸ KKP H P) (OmP H P) :=
  MulAction.compHom (OmP H P) <|
    QuotientGroup.lift (KKP H P) (MulAction.toPermHom ↥(NGP P) (OmP H P)) (le_refl _)

/-- The quotient action specialises to the action of `𝒢`. -/
@[simp] theorem quotient_smul_mk_OmP {H P : Subgroup G} (g : ↥(NGP P)) (ω : OmP H P) :
    (QuotientGroup.mk' (KKP H P) g) • ω = g • ω := rfl

theorem mem_KKP {H P : Subgroup G} {g : ↥(NGP P)} :
    g ∈ KKP H P ↔ ∀ ω : OmP H P, g • ω = ω := by
  rw [KKP, MonoidHom.mem_ker]
  constructor
  · intro h ω
    have h2 := congrArg (fun e : Equiv.Perm (OmP H P) => e ω) h
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply] at h2
    simpa using h2
  · intro h
    ext ω
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, h]
    rfl

theorem KKP_fixes {H P : Subgroup G} {g : ↥(NGP P)} (hg : g ∈ KKP H P) (ω : OmP H P) :
    g • ω = ω := (mem_KKP.mp hg) ω

/-! ## The base points `H` and `H^t` -/

/-- The base point `H` of `Ω_P`. -/
noncomputable def ptP (H P : Subgroup G) {t : G} (hP : P ≤ Submission.Blueprint.centD H t) :
    OmP H P :=
  ⟨(QuotientGroup.mk (1 : G) : G ⧸ H), Work.ThreePoints.pt_mem_fixedPts_of_le_centD hP⟩

/-- The point `H^t` of `Ω_P`. -/
noncomputable def pttP (H P : Subgroup G) {t : G} (hP : P ≤ Submission.Blueprint.centD H t) :
    OmP H P :=
  ⟨(QuotientGroup.mk t : G ⧸ H), Work.ThreePoints.mk_t_mem_fixedPts_of_le_centD hP⟩

@[simp] theorem coe_ptP (H P : Subgroup G) {t : G}
    (hP : P ≤ Submission.Blueprint.centD H t) :
    ((ptP H P hP : OmP H P) : G ⧸ H) = (QuotientGroup.mk (1 : G) : G ⧸ H) := rfl

@[simp] theorem coe_pttP (H P : Subgroup G) {t : G}
    (hP : P ≤ Submission.Blueprint.centD H t) :
    ((pttP H P hP : OmP H P) : G ⧸ H) = (QuotientGroup.mk t : G ⧸ H) := rfl

/-- The base point `H` is fixed by `g ∈ N_G(P)` exactly when `g ∈ H`. -/
theorem smul_ptP_eq_iff {H P : Subgroup G} {g : ↥(NGP P)} {t : G}
    (hP : P ≤ Submission.Blueprint.centD H t) :
    g • ptP H P hP = ptP H P hP ↔ (g : G) ∈ H := by
  constructor
  · intro h
    have h3 := congrArg (fun z : OmP H P => (z : G ⧸ H)) h
    simp only [coe_smul_OmP, coe_ptP, Work.ThreePoints.smul_mk] at h3
    have h4 : (((g : G) * 1)⁻¹ * (1 : G)) ∈ H := QuotientGroup.eq.mp h3
    have h5 : (g : G)⁻¹ ∈ H := by simpa using h4
    simpa using H.inv_mem h5
  · intro hg
    refine Subtype.ext ?_
    simp only [coe_smul_OmP, coe_ptP, Work.ThreePoints.smul_mk]
    exact QuotientGroup.eq.mpr (by simpa using H.inv_mem hg)

/-- The stabiliser of the base point in `𝒢 = N_G(P)` is `H ⊓ 𝒢`. -/
theorem stabilizer_ptP {H P : Subgroup G} {t : G}
    (hP : P ≤ Submission.Blueprint.centD H t) :
    MulAction.stabilizer ↥(NGP P) (ptP H P hP) =
      (H ⊓ NGP P).subgroupOf (NGP P) := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact Subgroup.mem_subgroupOf.mpr ⟨(smul_ptP_eq_iff hP).mp h, g.2⟩
  · intro hgh
    exact (smul_ptP_eq_iff hP).mpr (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hgh)).1

/-- The kernel of the action fixes the base point. -/
theorem KKP_le_subgroupOf {H P : Subgroup G} {t : G}
    (hP : P ≤ Submission.Blueprint.centD H t) :
    KKP H P ≤ (H ⊓ NGP P).subgroupOf (NGP P) := by
  intro g hg
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  refine ⟨?_, g.2⟩
  rw [← smul_ptP_eq_iff hP]
  exact KKP_fixes hg (ptP H P hP)

/-- The stabiliser of the base point in `𝒢 ⧸ KKP` is the image of `H ⊓ 𝒢`. -/
theorem stabilizer_ptP_quot {H P : Subgroup G} {t : G}
    (hP : P ≤ Submission.Blueprint.centD H t) :
    MulAction.stabilizer (↥(NGP P) ⧸ KKP H P) (ptP H P hP) =
      ((H ⊓ NGP P).subgroupOf (NGP P)).map (QuotientGroup.mk' (KKP H P)) := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (KKP H P) x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    rw [MulAction.mem_stabilizer_iff] at hx
    rw [quotient_smul_mk_OmP] at hx
    exact ⟨g, Subgroup.mem_subgroupOf.mpr ⟨(smul_ptP_eq_iff hP).mp hx, g.2⟩, rfl⟩
  · rintro ⟨y, hy, hyg⟩
    rw [MulAction.mem_stabilizer_iff, ← hyg, quotient_smul_mk_OmP]
    exact (smul_ptP_eq_iff hP).mpr
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).1

/-- The point `H^t` is fixed by `g ∈ N_G(P)` exactly when `g ∈ H^t = conj t H`. -/
theorem smul_pttP_eq_iff {H P : Subgroup G} {g : ↥(NGP P)} {t : G}
    (hP : P ≤ Submission.Blueprint.centD H t) :
    g • pttP H P hP = pttP H P hP ↔ (g : G) ∈ Submission.Blueprint.conj t H := by
  constructor
  · intro h
    have h3 := congrArg (fun z : OmP H P => (z : G ⧸ H)) h
    simp only [coe_smul_OmP, coe_pttP, Work.ThreePoints.smul_mk] at h3
    have h4 : (((g : G) * t)⁻¹ * t) ∈ H := QuotientGroup.eq.mp h3
    have h5 : t⁻¹ * (g : G)⁻¹ * t ∈ H := by
      have h6 : (((g : G) * t)⁻¹ * t) = t⁻¹ * (g : G)⁻¹ * t := by group
      rwa [h6] at h4
    have h7 : t⁻¹ * (g : G) * t ∈ H := by
      have h8 := H.inv_mem h5
      simpa [mul_assoc] using h8
    exact Work.ThreePoints.mem_conj_iff.mpr h7
  · intro hg
    refine Subtype.ext ?_
    simp only [coe_smul_OmP, coe_pttP, Work.ThreePoints.smul_mk]
    rw [QuotientGroup.eq]
    have h6 : t⁻¹ * (g : G) * t ∈ H := Work.ThreePoints.mem_conj_iff.mp hg
    have h7 : (((g : G) * t)⁻¹ * t) = t⁻¹ * (g : G)⁻¹ * t := by group
    rw [h7]
    have h8 := H.inv_mem h6
    simpa [mul_assoc] using h8

/-- The stabiliser of the point `H^t` in `𝒢 = N_G(P)` is `H^t ⊓ 𝒢`. -/
theorem stabilizer_pttP {H P : Subgroup G} {t : G}
    (hP : P ≤ Submission.Blueprint.centD H t) :
    MulAction.stabilizer ↥(NGP P) (pttP H P hP) =
      (Submission.Blueprint.conj t H ⊓ NGP P).subgroupOf (NGP P) := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact Subgroup.mem_subgroupOf.mpr ⟨(smul_pttP_eq_iff hP).mp h, g.2⟩
  · intro hgh
    exact (smul_pttP_eq_iff hP).mpr (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hgh)).1

/-- The stabiliser of the point `H^t` in `𝒢 ⧸ KKP` is the image of `H^t ⊓ 𝒢`. -/
theorem stabilizer_pttP_quot {H P : Subgroup G} {t : G}
    (hP : P ≤ Submission.Blueprint.centD H t) :
    MulAction.stabilizer (↥(NGP P) ⧸ KKP H P) (pttP H P hP) =
      ((Submission.Blueprint.conj t H ⊓ NGP P).subgroupOf (NGP P)).map
        (QuotientGroup.mk' (KKP H P)) := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (KKP H P) x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    rw [MulAction.mem_stabilizer_iff] at hx
    rw [quotient_smul_mk_OmP] at hx
    exact ⟨g, Subgroup.mem_subgroupOf.mpr ⟨(smul_pttP_eq_iff hP).mp hx, g.2⟩, rfl⟩
  · rintro ⟨y, hy, hyg⟩
    rw [MulAction.mem_stabilizer_iff, ← hyg, quotient_smul_mk_OmP]
    exact (smul_pttP_eq_iff hP).mpr
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).1

/-! ## The kernel lies in the two-point stabiliser `D = H ⊓ H^t` -/

/-- The image of the kernel in `G` lies in `H ⊓ H^t = twoPoint H t`. -/
theorem KKP_map_le_twoPoint {H P : Subgroup G} {t : G}
    (hP : P ≤ Submission.Blueprint.centD H t) :
    (KKP H P).map (NGP P).subtype ≤ Submission.Blueprint.twoPoint H t := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  have hfix := KKP_fixes hg (ptP H P hP)
  have h3 : (g : G) • (QuotientGroup.mk (1 : G) : G ⧸ H) = (QuotientGroup.mk (1 : G) : G ⧸ H) :=
    congrArg (fun z : OmP H P => (z : G ⧸ H)) hfix
  have hfixT := KKP_fixes hg (pttP H P hP)
  have h4 : (g : G) • (QuotientGroup.mk t : G ⧸ H) = (QuotientGroup.mk t : G ⧸ H) :=
    congrArg (fun z : OmP H P => (z : G ⧸ H)) hfixT
  rw [Submission.Blueprint.twoPoint, Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [Work.ThreePoints.smul_mk] at h3
    have h5 : (((g : G) * 1)⁻¹ * (1 : G)) ∈ H := QuotientGroup.eq.mp h3
    have h6 : (g : G)⁻¹ ∈ H := by simpa using h5
    simpa using H.inv_mem h6
  · rw [Work.ThreePoints.smul_mk] at h4
    have h5 : (((g : G) * t)⁻¹ * t) ∈ H := QuotientGroup.eq.mp h4
    have h6 : t⁻¹ * (g : G)⁻¹ * t ∈ H := by
      have h7 : (((g : G) * t)⁻¹ * t) = t⁻¹ * (g : G)⁻¹ * t := by group
      rwa [h7] at h5
    have h8 : t⁻¹ * (g : G) * t ∈ H := by
      have h9 := H.inv_mem h6
      simpa [mul_assoc] using h9
    exact Work.ThreePoints.mem_conj_iff.mpr h8

/-- The kernel has odd order (`H` is strongly embedded at `t ∉ H`, so `|H ⊓ H^t|` is odd). -/
theorem odd_card_KKP {H P : Subgroup G} {t : G} (hse : IsStronglyEmbedded H) (ht : t ∉ H)
    (hP : P ≤ Submission.Blueprint.centD H t) : Odd (Nat.card ↥(KKP H P)) := by
  have h1 : Nat.card ↥(KKP H P) = Nat.card ↥((KKP H P).map (NGP P).subtype) :=
    (Subgroup.card_map_of_injective (f := (NGP P).subtype) (K := KKP H P)
      Subtype.coe_injective).symm
  rw [h1]
  exact Odd.of_dvd_nat (hse.2.2 t ht)
    (Subgroup.card_dvd_of_le (KKP_map_le_twoPoint hP))

/-! ## `P₁ / P` cyclic, in a form that needs no quotient-group instance -/

/-- `P₁/P` is cyclic, stated elementarily: there is `x ∈ P₁` such that every element of `P₁` is a
product `x^k * q` with `q ∈ P` (equivalently `P₁ = ⟨x⟩ P`, i.e. `P₁/P` is generated by the image
of `x`, when `P ⊴ P₁`).  Natural-number exponents suffice because `x⁻¹` is a positive power of
`x`. -/
def IsCyclicMod (P P₁ : Subgroup G) : Prop :=
  ∃ x ∈ P₁, ∀ y ∈ P₁, ∃ (k : ℕ) (q : G), q ∈ P ∧ y = x ^ k * q

end Work.NormalComplement.S5K
