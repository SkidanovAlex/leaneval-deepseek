import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.S02
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.pieceAInv
import Submission.Work.BG.rem31Structure
import Submission.Work.BG.sconjLam

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup

variable {G : Type} [Group G] [Finite G]

/-- Conjugation by `s` on `↥(Uin C)`. -/
noncomputable def sigmaUinDef (C : Sec2Ctx G) : ↥(Uin C) ≃* ↥(Uin C) where
  toFun x := ⟨conjMulEquiv C.P C.s (x : ↥C.P.H0), by
    rw [mem_subgroupOf]
    exact conj_mem_U C (mem_subgroupOf.mp x.2)⟩
  invFun x := ⟨conjMulEquiv C.P C.s (x : ↥C.P.H0), by
    rw [mem_subgroupOf]
    exact conj_mem_U C (mem_subgroupOf.mp x.2)⟩
  left_inv x := by
    apply Subtype.ext; apply Subtype.ext
    show ((C.s : G) * ((C.s : G) * (x : G) * (C.s : G)⁻¹) * (C.s : G)⁻¹) = (x : G)
    have hs := s_mul_self_coe C
    calc (C.s : G) * ((C.s : G) * (x : G) * (C.s : G)⁻¹) * (C.s : G)⁻¹
        = ((C.s : G) * (C.s : G)) * (x : G) * ((C.s : G)⁻¹ * (C.s : G)⁻¹) := by group
      _ = (x : G) := by rw [hs, one_mul, ← mul_inv_rev, hs, inv_one, mul_one]
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext
    show ((C.s : G) * ((C.s : G) * (x : G) * (C.s : G)⁻¹) * (C.s : G)⁻¹) = (x : G)
    have hs := s_mul_self_coe C
    calc (C.s : G) * ((C.s : G) * (x : G) * (C.s : G)⁻¹) * (C.s : G)⁻¹
        = ((C.s : G) * (C.s : G)) * (x : G) * ((C.s : G)⁻¹ * (C.s : G)⁻¹) := by group
      _ = (x : G) := by rw [hs, one_mul, ← mul_inv_rev, hs, inv_one, mul_one]
  map_mul' x y := by
    apply Subtype.ext; apply Subtype.ext
    show ((C.s : G) * ((x : G) * (y : G)) * (C.s : G)⁻¹)
        = ((C.s : G) * (x : G) * (C.s : G)⁻¹) * ((C.s : G) * (y : G) * (C.s : G)⁻¹)
    group

@[simp] theorem sigmaUinDef_apply_coe (C : Sec2Ctx G) (x : ↥(Uin C)) :
    ((sigmaUinDef C x : ↥(Uin C)) : G) = (C.s : G) * (x : G) * (C.s : G)⁻¹ := rfl

/-- `λ_β = 1` on `U`. -/
theorem lamCF_apply_mem_U (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ) (x : ↥(Uin C)) :
    lamCF C β (x : ↥C.P.H0) = 1 := by
  have hx : (x : ↥C.P.H0) ∈ C.P.U.subgroupOf C.P.H0 := x.2
  have hq : quotMk C.P (x : ↥C.P.H0) = 1 :=
    (QuotientGroup.eq_one_iff (x : ↥C.P.H0)).mpr (by rwa [mem_subgroupOf] at hx)
  rw [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply, hq, map_one]
  rfl

/-- `b_u := μ|_U` is `sigmaUinDef`-invariant when `μ^s ∈ Λμ`. -/
theorem restrictUin_sigmaUin_invariant [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {μ : ClassFunction ↥C.P.H0 ℂ} (hm : sconj C μ ∈ lamOrbit C μ) :
    ClassFunction.compHom (sigmaUinDef C).toMonoidHom (ClassFunction.restrict (Uin C) μ)
      = ClassFunction.restrict (Uin C) μ := by
  obtain ⟨β, hβ⟩ := hm
  ext x
  show μ ((sigmaUinDef C x : ↥(Uin C)) : ↥C.P.H0) = μ (x : ↥C.P.H0)
  rw [show ((sigmaUinDef C x : ↥(Uin C)) : ↥C.P.H0)
        = conjMulEquiv C.P C.s (x : ↥C.P.H0) from rfl]
  rw [← conjByH_apply C.P C.s μ (x : ↥C.P.H0)]
  rw [show conjByH C.P C.s μ (x : ↥C.P.H0) = sconj C μ (x : ↥C.P.H0) from rfl]
  rw [hβ, ClassFunction.mul_apply, lamCF_apply_mem_U, one_mul]

/-- `S₀` centralizes `K` when both `t₁` and `t₂` invert `K`. -/
theorem S0_centralizes_K (D : BGData G) (K : Subgroup G)
    (hKinv1 : ∀ x ∈ K, D.t1 * x * D.t1⁻¹ = x⁻¹)
    (hKinv2 : ∀ x ∈ K, D.t2 * x * D.t2⁻¹ = x⁻¹) :
    ∀ s ∈ D.S0, ∀ x ∈ K, s * x * s⁻¹ = x := by
  intro s hs x hx
  have h12 : (D.t1 * D.t2) * x = x * (D.t1 * D.t2) := by
    have key : (D.t1 * D.t2) * x * (D.t1 * D.t2)⁻¹ = x := by
      rw [mul_inv_rev]
      calc (D.t1 * D.t2) * x * (D.t2⁻¹ * D.t1⁻¹)
          = D.t1 * (D.t2 * x * D.t2⁻¹) * D.t1⁻¹ := by group
        _ = D.t1 * x⁻¹ * D.t1⁻¹ := by rw [hKinv2 x hx]
        _ = (D.t1 * x * D.t1⁻¹)⁻¹ := by group
        _ = (x⁻¹)⁻¹ := by rw [hKinv1 x hx]
        _ = x := by group
    calc (D.t1 * D.t2) * x
        = ((D.t1 * D.t2) * x * (D.t1 * D.t2)⁻¹) * (D.t1 * D.t2) := by group
      _ = x * (D.t1 * D.t2) := by rw [key]
  have hmem : (D.t1 * D.t2) ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]; exact h12
  have hle : D.S0 ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [D.gen]; exact Subgroup.zpowers_le.mpr hmem
  have hs' := hle hs
  rw [Subgroup.mem_centralizer_singleton_iff] at hs'
  rw [hs']; group

/-- The image of `K` in `↥(Uin C)`. -/
abbrev KuSub (C : Sec2Ctx G) (K : Subgroup G) : Subgroup ↥(Uin C) :=
  (K.subgroupOf C.P.H0).subgroupOf (Uin C)

theorem KuSub_normal (D : BGData G) (C : Sec2Ctx G) (K : Subgroup G)
    (hKnorm : ∀ u ∈ C.P.U, ∀ x ∈ K, u * x * u⁻¹ ∈ K) :
    (KuSub C K).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hkK : ((n : ↥(Uin C)) : G) ∈ K := by
    have h := hn; rw [KuSub, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h; exact h
  have hgU : ((g : ↥(Uin C)) : G) ∈ C.P.U := by
    have h := (g : ↥(Uin C)).2; rwa [Subgroup.mem_subgroupOf] at h
  show g * n * g⁻¹ ∈ KuSub C K
  rw [KuSub, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  show ((g * n * g⁻¹ : ↥(Uin C)) : G) ∈ K
  rw [show ((g * n * g⁻¹ : ↥(Uin C)) : G) = (g:G) * (n:G) * (g:G)⁻¹ from rfl]
  exact hKnorm (g:G) hgU (n:G) hkK

theorem sigmaUinDef_inverts_Ku (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (K : Subgroup G) (hKinv1 : ∀ x ∈ K, D.t1 * x * D.t1⁻¹ = x⁻¹) :
    ∀ k ∈ KuSub C K, sigmaUinDef C k = k⁻¹ := by
  intro k hk
  have hkK : ((k : ↥(Uin C)) : G) ∈ K := by
    have h := hk; rw [KuSub, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h; exact h
  apply Subtype.ext; apply Subtype.ext
  rw [sigmaUinDef_apply_coe, hDC.s_eq, hKinv1 ((k:↥(Uin C)) : G) hkK]
  rfl

theorem conjNormal_S0_centralizes_Ku (D : BGData G) (C : Sec2Ctx G) (K : Subgroup G)
    (hKinv1 : ∀ x ∈ K, D.t1 * x * D.t1⁻¹ = x⁻¹)
    (hKinv2 : ∀ x ∈ K, D.t2 * x * D.t2⁻¹ = x⁻¹)
    {z : ↥C.P.H0} (hz : z ∈ D.S0.subgroupOf C.P.H0) :
    ∀ k ∈ KuSub C K, MulAut.conjNormal z k = k := by
  intro k hk
  have hzS0 : (z : G) ∈ D.S0 := by
    have h := hz; rw [Subgroup.mem_subgroupOf] at h; exact h
  have hkK : ((k : ↥(Uin C)) : G) ∈ K := by
    have h := hk; rw [KuSub, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h; exact h
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  apply Subtype.ext
  exact S0_centralizes_K D K hKinv1 hKinv2 (z:G) hzS0 ((k:↥(Uin C)):G) hkK

theorem sup_Uin_S0 (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C) :
    Uin C ⊔ D.S0.subgroupOf C.P.H0 = ⊤ := by
  have hUleH0 : D.U ≤ C.P.H0 := by rw [← hDC.U_eq]; exact C.P.U_le_H0
  have hS0leH0 : D.S0 ≤ C.P.H0 := by rw [hDC.H0_eq]; exact le_sup_right
  have h1 : (D.U ⊔ D.S0).subgroupOf C.P.H0 = Uin C ⊔ D.S0.subgroupOf C.P.H0 := by
    rw [Subgroup.subgroupOf_sup hUleH0 hS0leH0, show D.U = C.P.U from hDC.U_eq.symm]
  have h2 : (D.U ⊔ D.S0).subgroupOf C.P.H0 = ⊤ := by
    rw [show C.P.H0 = D.U ⊔ D.S0 from hDC.H0_eq, Subgroup.subgroupOf_self]
  rw [← h1, h2]

theorem odd_card_Uin (D : BGData G) (C : Sec2Ctx G) [Fintype G]
    (hDC : Compat D C) : Odd (Nat.card ↥(Uin C)) := by
  haveI : Fintype ↥(Uin C) := Fintype.ofFinite _
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe C.P.U_le_H0).toEquiv]
  exact odd_card_U_of_compat hDC

/-- Key reduction: every irreducible constituent `θ` of `μ|_U` is trivial on `K`, when
`μ^s ∈ Λμ`. -/
theorem constituent_trivial_of_sconj_mem [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype ↥(Uin C)] [Invertible (Nat.card ↥(Uin C) : ℂ)] (K : Subgroup G)
    (hDC : Compat D C)
    (hKnorm : ∀ u ∈ C.P.U, ∀ x ∈ K, u * x * u⁻¹ ∈ K)
    (hKinv1 : ∀ x ∈ K, D.t1 * x * D.t1⁻¹ = x⁻¹)
    (hKinv2 : ∀ x ∈ K, D.t2 * x * D.t2⁻¹ = x⁻¹)
    {μ : ClassFunction ↥C.P.H0 ℂ} (hμ : IsIrreducibleCharacter μ)
    (hm : sconj C μ ∈ lamOrbit C μ)
    {θ : ClassFunction ↥(Uin C) ℂ} (hθ : IsIrreducibleCharacter θ)
    (hconst : ClassFunction.inner (ClassFunction.restrict (Uin C) μ) θ ≠ 0) :
    ∀ k ∈ KuSub C K, θ k = θ 1 := by
  classical
  let θI : IrreducibleCharacter ↥(Uin C) := ⟨θ, hθ⟩
  let σθI : IrreducibleCharacter ↥(Uin C) :=
    ⟨ClassFunction.compHom (sigmaUinDef C).toMonoidHom θ,
      IsIrreducibleCharacter.compHom_of_surjective (sigmaUinDef C).surjective hθ⟩
  have hσinv : ClassFunction.compHom (sigmaUinDef C).toMonoidHom (ClassFunction.restrict (Uin C) μ)
      = ClassFunction.restrict (Uin C) μ := restrictUin_sigmaUin_invariant D C hm
  haveI hKunorm : (KuSub C K).Normal := KuSub_normal D C K hKnorm
  have hconstσ : ClassFunction.inner (ClassFunction.restrict (Uin C) μ)
      (ClassFunction.compHom (sigmaUinDef C).toMonoidHom θ) ≠ 0 := by
    rw [← hσinv, ClassFunction.inner_compHom_mulEquiv]
    exact hconst
  obtain ⟨g, hg⟩ :=
    IrreducibleCharacter.RestrictionConstituentsSingleOrbit.exists_conj (H := Uin C)
      (restrictionConstituentsSingleOrbit_of_isIrreducible (H := Uin C)
        (⟨μ, hμ⟩ : IrreducibleCharacter ↥C.P.H0))
      (show IrreducibleCharacter.LiesOver (Uin C) (⟨μ, hμ⟩ : IrreducibleCharacter ↥C.P.H0) θI
        from hconst)
      (show IrreducibleCharacter.LiesOver (Uin C) (⟨μ, hμ⟩ : IrreducibleCharacter ↥C.P.H0) σθI
        from hconstσ)
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp
      (by rw [sup_Uin_S0 D C hDC]; exact Subgroup.mem_top g)
  -- `g = y * z` with `y ∈ Uin C`, `z ∈ S₀`; `y` acts trivially on `θ`
  have hy_fix_cf : ClassFunction.conjBy y θ = θ := ClassFunction.conjBy_eq_self_of_mem hy θ
  have hgz : IrreducibleCharacter.conjBy (y * z) θI = σθI := by rw [hyz]; exact hg
  have hgz_cf : ClassFunction.conjBy (y * z) θ
      = ClassFunction.compHom (sigmaUinDef C).toMonoidHom θ := by
    have h2' := congrArg (fun χ : IrreducibleCharacter ↥(Uin C) =>
      (χ : ClassFunction ↥(Uin C) ℂ)) hgz
    rw [IrreducibleCharacter.coe_conjBy] at h2'
    change ClassFunction.conjBy (y * z) θ
      = ClassFunction.compHom (sigmaUinDef C).toMonoidHom θ at h2'
    exact h2'
  have hz_conj_cf : ClassFunction.conjBy z θ
      = ClassFunction.compHom (sigmaUinDef C).toMonoidHom θ := by
    rw [ClassFunction.conjBy_mul, hy_fix_cf] at hgz_cf
    exact hgz_cf
  intro k hk
  have hz1mem : z⁻¹ ∈ D.S0.subgroupOf C.P.H0 := Subgroup.inv_mem _ hz
  refine pieceAInv (KuSub C K) (odd_card_Uin D C hDC)
    (sigmaUinDef C * MulAut.conjNormal z⁻¹) ?_ θ hθ ?_ k hk
  · intro k hk
    rw [MulAut.mul_apply,
      conjNormal_S0_centralizes_Ku D C K hKinv1 hKinv2 hz1mem k hk,
      sigmaUinDef_inverts_Ku D C hDC K hKinv1 k hk]
  · intro u
    rw [MulAut.mul_apply]
    have hv := congrArg (fun φ : ClassFunction ↥(Uin C) ℂ =>
      φ (MulAut.conjNormal z⁻¹ u)) hz_conj_cf
    rw [show ClassFunction.compHom (sigmaUinDef C).toMonoidHom θ (MulAut.conjNormal z⁻¹ u)
        = θ (sigmaUinDef C (MulAut.conjNormal z⁻¹ u)) from rfl] at hv
    rw [← hv]
    rw [ClassFunction.conjBy_apply]
    change θ (MulAut.conjNormal z (MulAut.conjNormal z⁻¹ u)) = θ u
    rw [← MulAut.mul_apply, show MulAut.conjNormal z * MulAut.conjNormal z⁻¹ = 1 from by
      rw [← map_mul, mul_inv_cancel, map_one]]
    rfl

theorem L36SconjNotInOrbit {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype ↥C.P.H0] (K : Subgroup G)
    (hDC : Work.GW2.C16.Compat D C) (hS3 : Work.GW2.C16.Sec3Hyp D)
    (hKU : K ≤ C.P.U) (hKnorm : ∀ u ∈ C.P.U, ∀ x ∈ K, u * x * u⁻¹ ∈ K)
    (hKinv1 : ∀ x ∈ K, D.t1 * x * D.t1⁻¹ = x⁻¹)
    (hKinv2 : ∀ x ∈ K, D.t2 * x * D.t2⁻¹ = x⁻¹)
    (μ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ)
    (hμ : OddOrder.RepresentationTheory.IsIrreducibleCharacter μ)
    (hKμ : ∃ u : ↥C.P.H0, (u : G) ∈ K ∧ μ u ≠ μ 1) :
    Work.BG.sconj C μ ∉ Work.BG.lamOrbit C μ := by
  intro hm
  haveI hFinU : Fintype ↥(Uin C) := Fintype.ofFinite _
  haveI hInvU : Invertible (Nat.card ↥(Uin C) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨u, huK, hune⟩ := hKμ
  have huU : u ∈ Uin C := by rw [mem_subgroupOf]; exact hKU huK
  let k : ↥(Uin C) := ⟨u, huU⟩
  have hkKu : k ∈ KuSub C K := by
    rw [KuSub, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact huK
  have hbk : ClassFunction.restrict (Uin C) μ k ≠ ClassFunction.restrict (Uin C) μ 1 := by
    rw [ClassFunction.restrict_apply, ClassFunction.restrict_apply]
    simpa [k] using hune
  obtain ⟨a, ha, hcase⟩ := rem31Shape D C hDC hS3 μ hμ
  have h11 : ClassFunction.inner a a = 1 := by
    have := irreducibleCharacter_inner_eq_ite (⟨a, ha⟩ : IrreducibleCharacter ↥(Uin C))
      (⟨a, ha⟩ : IrreducibleCharacter ↥(Uin C))
    simpa using this
  rcases hcase with ⟨ha_eq, _⟩ | ⟨a₂, ha₂, hne, _, ha_eq, _⟩
  · have hconst : ClassFunction.inner (ClassFunction.restrict (Uin C) μ) a ≠ 0 := by
      rw [ha_eq, h11]; exact one_ne_zero
    have htriv := constituent_trivial_of_sconj_mem D C K hDC hKnorm hKinv1 hKinv2 hμ hm ha
      hconst k hkKu
    rw [ha_eq, htriv] at hbk
    exact hbk rfl
  · have h20 : ClassFunction.inner a₂ a = 0 := by
      have := irreducibleCharacter_inner_eq_ite (⟨a₂, ha₂⟩ : IrreducibleCharacter ↥(Uin C))
        (⟨a, ha⟩ : IrreducibleCharacter ↥(Uin C))
      rw [if_neg (fun h => hne (congrArg Subtype.val h))] at this
      simpa using this
    have hconsta : ClassFunction.inner (ClassFunction.restrict (Uin C) μ) a ≠ 0 := by
      rw [ha_eq, ClassFunction.inner_add_left, h11, h20]; norm_num
    have h12 : ClassFunction.inner a₂ a₂ = 1 := by
      have := irreducibleCharacter_inner_eq_ite (⟨a₂, ha₂⟩ : IrreducibleCharacter ↥(Uin C))
        (⟨a₂, ha₂⟩ : IrreducibleCharacter ↥(Uin C))
      simpa using this
    have h01 : ClassFunction.inner a a₂ = 0 := by
      have := irreducibleCharacter_inner_eq_ite (⟨a, ha⟩ : IrreducibleCharacter ↥(Uin C))
        (⟨a₂, ha₂⟩ : IrreducibleCharacter ↥(Uin C))
      rw [if_neg (fun h => hne (congrArg Subtype.val h.symm))] at this
      simpa using this
    have hconsta₂ : ClassFunction.inner (ClassFunction.restrict (Uin C) μ) a₂ ≠ 0 := by
      rw [ha_eq, ClassFunction.inner_add_left, h01, h12]; norm_num
    have hta := constituent_trivial_of_sconj_mem D C K hDC hKnorm hKinv1 hKinv2 hμ hm ha
      hconsta k hkKu
    have hta₂ := constituent_trivial_of_sconj_mem D C K hDC hKnorm hKinv1 hKinv2 hμ hm ha₂
      hconsta₂ k hkKu
    rw [ha_eq, ClassFunction.add_apply, ClassFunction.add_apply] at hbk
    rw [hta, hta₂] at hbk
    exact hbk rfl

end Work.BG
