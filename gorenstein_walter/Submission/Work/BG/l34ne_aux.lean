import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma24
import Submission.Work.BG.centralIntegral
import Submission.Work.BG.glaubValue
import Submission.Work.BG.lemma18LinearIndependent
import Submission.Work.BG.rem31Orth
import Submission.Work.BG.rem31StabCard
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.CharBridge
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.modTwoIndep
import Submission.Work.BG.lemma33Aux
import Submission.Work.BG.lemma33ShapeA
import Submission.Work.BG.lemma33Plumb
import Submission.Work.BG.congContra
import Submission.Work.BG.l34ne_glauberman_contra
import Submission.Work.BG.l34ne_chi_even
import Submission.Work.BG.l34ne_deg_mod_four
import Submission.Work.BG.l34ne_restrict_shape

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-! ## Preliminary bookkeeping for `l34Exc_sfixed_ne_four` -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- `𝒮(χ) = bset C f χ` is stable under `s`-conjugation (coherence clause (ii)). -/
theorem l34ne_sconj_mem_bset (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) {η : ClassFunction ↥C.P.H0 ℂ} (hη : η ∈ bset C f χ) :
    sconj C η ∈ bset C f χ := by
  refine ⟨IsIrreducibleCharacter.conjByH C.P C.s hη.1, ?_⟩
  have hk : η ∈ orbitKey C η := Or.inl (s02c_LamEquiv_refl C η)
  have hfix : f (sconj C η) = f η := ((hf.1 η hη.1) η hk η hk hη.1 hη.1).2.1
  rw [hfix]
  exact hη.2

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- In the standing configuration `Λν` is `s`-stable with `ν^s ≠ ν` and `|Λν| = 4`, so the
standing disjunction forces `D.n = 4`. -/
theorem l34ne_n_eq_four (D : Work.GW2.BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {ν : ClassFunction ↥C.P.H0 ℂ}
    (hdisj : sconj C ν ∉ lamOrbit C ν ∨ (lamOrbit C ν).ncard = D.n)
    (hinv : sconj C '' lamOrbit C ν = lamOrbit C ν)
    (h4 : (lamOrbit C ν).ncard = 4) : D.n = 4 := by
  have hm : ν ∈ lamOrbit C ν := mem_lamOrbit_self C ν
  have hs : sconj C ν ∈ sconj C '' lamOrbit C ν := ⟨ν, hm, rfl⟩
  rw [hinv] at hs
  rcases hdisj with h | h
  · exact absurd hs h
  · rw [h4] at h
    exact h.symm

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- `𝒮(χ) = {ν, ν^s, ξ}` in the standing configuration. -/
theorem l34ne_bset_eq (D : Work.GW2.BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hDC : Compat D C) (hS3 : Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    {ν ξ : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ bset C f χ) (hne : sconj C ν ≠ ν)
    (hξ : ξ ∈ bset C f χ) (hξν : ξ ≠ ν) (hξνs : ξ ≠ sconj C ν) :
    bset C f χ = {ν, sconj C ν, ξ} := by
  have h2 : sconj C ν ∈ bset C f χ := l34ne_sconj_mem_bset C f hf χ hν
  have hsub : ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset C f χ := by
    intro η hη
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hη
    rcases hη with rfl | rfl | rfl
    · exact hν
    · exact h2
    · exact hξ
  have hsν : sconj C ν ≠ ν := hne
  have h1 : ν ∉ ({sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hsν h.symm, fun h => hξν h.symm⟩
  have h2' : sconj C ν ∉ ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    simp only [Set.mem_singleton_iff]
    exact fun h => hξνs h.symm
  have hcard : ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 3 := by
    rw [show ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ))
        = insert ν (insert (sconj C ν) ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ))) from rfl,
      Set.ncard_insert_of_notMem h1 (Set.toFinite _),
      Set.ncard_insert_of_notMem h2' (Set.toFinite _), Set.ncard_singleton]
  have hle : (bset C f χ).ncard ≤ 3 := thm32 D C hDC hS3 f hf χ hχ
  have hfin : (bset C f χ).Finite := s02_bset_finite C f χ
  have hge : 3 ≤ (bset C f χ).ncard := by
    rw [← hcard]
    exact Set.ncard_le_ncard hsub hfin
  have hb : (bset C f χ).ncard ≤ ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard := by
    rw [hcard]; exact hle
  exact (Set.eq_of_subset_of_ncard_le hsub hb hfin).symm

/-! ## Conjugation automorphisms of `U = C.P.U` -/

theorem l34ne_conj_mem_U_of_mem_H (D : BGData G) {g u : G} (hg : g ∈ D.H) (hu : u ∈ D.U) :
    g * u * g⁻¹ ∈ D.U :=
  (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_U D hg) u).mp hu

/-- Conjugation by an element `g ∈ D.H`, as an automorphism of `U = C.P.U`. -/
noncomputable def l34ne_conjU (D : BGData G) (C : Sec2Ctx G) (hc : Compat D C) {g : G}
    (hg : g ∈ D.H) : MulAut ↥C.P.U where
  toFun u := ⟨g * (u : G) * g⁻¹, by
    have hu : (u : G) ∈ D.U := by simpa only [hc.U_eq] using u.2
    have h := l34ne_conj_mem_U_of_mem_H D hg hu
    simpa only [hc.U_eq] using h⟩
  invFun u := ⟨g⁻¹ * (u : G) * g, by
    have hu : (u : G) ∈ D.U := by simpa only [hc.U_eq] using u.2
    have h := l34ne_conj_mem_U_of_mem_H D (D.H.inv_mem hg) hu
    simpa only [hc.U_eq, inv_inv] using h⟩
  left_inv u := by
    apply Subtype.ext
    show g⁻¹ * (g * (u : G) * g⁻¹) * g = (u : G)
    group
  right_inv u := by
    apply Subtype.ext
    show g * (g⁻¹ * (u : G) * g) * g⁻¹ = (u : G)
    group
  map_mul' u v := by
    apply Subtype.ext
    show g * ((u : G) * (v : G)) * g⁻¹ = (g * (u : G) * g⁻¹) * (g * (v : G) * g⁻¹)
    group

@[simp] theorem l34ne_conjU_apply_coe (D : BGData G) (C : Sec2Ctx G) (hc : Compat D C)
    {g : G} (hg : g ∈ D.H) (u : ↥C.P.U) :
    ((l34ne_conjU D C hc hg u : ↥C.P.U) : G) = g * (u : G) * g⁻¹ := rfl

theorem l34ne_t_mem_H (D : BGData G) : D.t ∈ D.H :=
  Subgroup.mem_centralizer_iff.mpr (fun h hh => by
    rw [Set.mem_singleton_iff] at hh
    rw [hh])

theorem l34ne_t2_mem_H (D : BGData G) : D.t2 ∈ D.H := BGData_S_le_centralizer_t D D.t2_mem
theorem l34ne_t1_mem_H (D : BGData G) : D.t1 ∈ D.H := BGData_S_le_centralizer_t D D.t1_mem
theorem l34ne_t1t2_mem_H (D : BGData G) : D.t1 * D.t2 ∈ D.H :=
  D.H.mul_mem (l34ne_t1_mem_H D) (l34ne_t2_mem_H D)

theorem l34ne_t1t2_mem_H0 (D : BGData G) (C : Sec2Ctx G) (hc : Compat D C) :
    D.t1 * D.t2 ∈ C.P.H0 := by
  have h1 : D.t1 * D.t2 ∈ H1 D := by
    refine Subgroup.mem_sup_right ?_
    rw [D.gen]
    exact Subgroup.mem_zpowers _
  simpa [← hc.H0_eq] using h1

theorem l34ne_mul_self_eq_one (D : BGData G) {g : G} (h : orderOf g = 2) : g * g = 1 := by
  have h2 : g ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [h])
  simpa [pow_two] using h2

theorem l34ne_t2_eq (D : BGData G) : D.t2 = D.t1 * (D.t1 * D.t2) := by
  rw [← mul_assoc, l34ne_mul_self_eq_one D D.t1_order, one_mul]

/-- Conjugation by `t₂`. -/
noncomputable abbrev l34ne_sig2 (D : BGData G) (C : Sec2Ctx G) (hc : Compat D C) : MulAut ↥C.P.U :=
  l34ne_conjU D C hc (l34ne_t2_mem_H D)

/-- Conjugation by `t₁t₂`. -/
noncomputable abbrev l34ne_sigx (D : BGData G) (C : Sec2Ctx G) (hc : Compat D C) : MulAut ↥C.P.U :=
  l34ne_conjU D C hc (l34ne_t1t2_mem_H D)

@[simp] theorem l34ne_sig2_apply_coe (D : BGData G) (C : Sec2Ctx G) (hc : Compat D C)
    (u : ↥C.P.U) :
    ((l34ne_sig2 D C hc u : ↥C.P.U) : G) = D.t2 * (u : G) * D.t2⁻¹ := rfl

@[simp] theorem l34ne_sigx_apply_coe (D : BGData G) (C : Sec2Ctx G) (hc : Compat D C)
    (u : ↥C.P.U) :
    ((l34ne_sigx D C hc u : ↥C.P.U) : G) = (D.t1 * D.t2) * (u : G) * (D.t1 * D.t2)⁻¹ := rfl

theorem l34ne_conjU_mul (D : BGData G) (C : Sec2Ctx G) (hc : Compat D C) {g h : G}
    (hg : g ∈ D.H) (hh : h ∈ D.H) {gh : G} (hgh : gh = g * h) (hghH : gh ∈ D.H) :
    l34ne_conjU D C hc hg * l34ne_conjU D C hc hh = l34ne_conjU D C hc hghH := by
  refine MulEquiv.ext fun u => ?_
  apply Subtype.ext
  show g * (h * (u : G) * h⁻¹) * g⁻¹ = gh * (u : G) * gh⁻¹
  rw [hgh]
  group

theorem l34ne_conjU_eq_one (D : BGData G) (C : Sec2Ctx G) (hc : Compat D C) {g : G}
    (hg : g ∈ D.H) (hcU : ∀ u ∈ D.U, g * u = u * g) : l34ne_conjU D C hc hg = 1 := by
  refine MulEquiv.ext fun u => ?_
  apply Subtype.ext
  have huD : (u : G) ∈ D.U := by simpa only [hc.U_eq] using u.2
  show g * (u : G) * g⁻¹ = (u : G)
  rw [hcU (u : G) huD]
  group

theorem l34ne_sig2_mul_self (D : BGData G) (C : Sec2Ctx G) (hc : Compat D C) :
    l34ne_sig2 D C hc * l34ne_sig2 D C hc = 1 := by
  have hsq : D.t2 * D.t2 = 1 := l34ne_mul_self_eq_one D D.t2_order
  rw [l34ne_conjU_mul D C hc (l34ne_t2_mem_H D) (l34ne_t2_mem_H D) hsq.symm D.H.one_mem]
  exact l34ne_conjU_eq_one D C hc D.H.one_mem (fun u _ => by group)

theorem l34ne_sigx_mul_self (D : BGData G) (C : Sec2Ctx G) (hc : Compat D C)
    (hS3 : Sec3Hyp D) : l34ne_sigx D C hc * l34ne_sigx D C hc = 1 := by
  have hx : D.t1 * D.t2 ∈ D.S0 := by rw [D.gen]; exact Subgroup.mem_zpowers _
  have hmem : (D.t1 * D.t2) * (D.t1 * D.t2) ∈ D.H :=
    D.H.mul_mem (l34ne_t1t2_mem_H D) (l34ne_t1t2_mem_H D)
  rw [l34ne_conjU_mul D C hc (l34ne_t1t2_mem_H D) (l34ne_t1t2_mem_H D) rfl hmem]
  exact l34ne_conjU_eq_one D C hc hmem (fun u hu => by
    have := hS3 (D.t1 * D.t2) hx u hu
    simpa [pow_two] using this)

theorem l34ne_sig2_eq (D : BGData G) (C : Sec2Ctx G) (hc : Compat D C) :
    l34ne_sig2 D C hc = sigmaU C * l34ne_sigx D C hc := by
  refine MulEquiv.ext fun u => ?_
  apply Subtype.ext
  show D.t2 * (u : G) * D.t2⁻¹
      = (C.s : G) * ((D.t1 * D.t2) * (u : G) * (D.t1 * D.t2)⁻¹) * (C.s : G)⁻¹
  rw [hc.s_eq]
  conv_lhs => rw [l34ne_t2_eq D]
  group

theorem l34ne_sigx_eq (D : BGData G) (C : Sec2Ctx G) (hc : Compat D C) :
    l34ne_sigx D C hc = sigmaU C * l34ne_sig2 D C hc := by
  rw [l34ne_sig2_eq D C hc, ← mul_assoc, sigmaU_mul_self C, one_mul]

/-- `compHom` of a product of automorphisms is the composite. -/
theorem l34ne_compHom_mul {U : Type} [Group U] (τ σ : MulAut U) (α : ClassFunction U ℂ) :
    ClassFunction.compHom (τ * σ).toMonoidHom α
      = ClassFunction.compHom σ.toMonoidHom (ClassFunction.compHom τ.toMonoidHom α) := by
  ext u
  simp [ClassFunction.compHom_apply]

/-! ## `s`-stability of `ξ|_U` -/

theorem l34ne_restrictU_sigmaU_apply (C : Sec2Ctx G) {ξ : ClassFunction ↥C.P.H0 ℂ}
    (hfix : sconj C ξ = ξ) (u : ↥C.P.U) :
    restrictU C ξ (sigmaU C u) = restrictU C ξ u := by
  have hfix' : conjByH C.P C.s ξ = ξ := hfix
  have hkey : conjMulEquiv C.P C.s (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0)
      = (⟨((sigmaU C u : ↥C.P.U) : G), C.P.U_le_H0 (sigmaU C u).2⟩ : ↥C.P.H0) :=
    Subtype.ext (by rw [conjMulEquiv_apply, sigmaU_apply_coe])
  calc restrictU C ξ (sigmaU C u)
      = ξ (⟨((sigmaU C u : ↥C.P.U) : G), C.P.U_le_H0 (sigmaU C u).2⟩ : ↥C.P.H0) := rfl
    _ = ξ (conjMulEquiv C.P C.s (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0)) := by rw [hkey]
    _ = conjByH C.P C.s ξ (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0) := rfl
    _ = ξ (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0) := by rw [hfix']
    _ = restrictU C ξ u := rfl

theorem l34ne_restrictU_sigmaU (C : Sec2Ctx G) {ξ : ClassFunction ↥C.P.H0 ℂ}
    (hfix : sconj C ξ = ξ) :
    ClassFunction.compHom (sigmaU C).toMonoidHom (restrictU C ξ) = restrictU C ξ := by
  ext u
  rw [ClassFunction.compHom_apply]
  exact l34ne_restrictU_sigmaU_apply C hfix u

theorem l34ne_restrictU_sigx_apply (D : BGData G) (C : Sec2Ctx G) (hc : Compat D C)
    (ξ : ClassFunction ↥C.P.H0 ℂ) (u : ↥C.P.U) :
    restrictU C ξ (l34ne_sigx D C hc u) = restrictU C ξ u := by
  have hEl : (⟨((l34ne_sigx D C hc u : ↥C.P.U) : G),
        C.P.U_le_H0 (l34ne_sigx D C hc u).2⟩ : ↥C.P.H0)
      = (⟨D.t1 * D.t2, l34ne_t1t2_mem_H0 D C hc⟩ : ↥C.P.H0)
        * (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0)
        * (⟨D.t1 * D.t2, l34ne_t1t2_mem_H0 D C hc⟩ : ↥C.P.H0)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, l34ne_sigx_apply_coe]
  rw [restrictU_apply, restrictU_apply, hEl, ClassFunction.conj_eq]

theorem l34ne_restrictU_sigx (D : BGData G) (C : Sec2Ctx G) (hc : Compat D C)
    (ξ : ClassFunction ↥C.P.H0 ℂ) :
    ClassFunction.compHom (l34ne_sigx D C hc).toMonoidHom (restrictU C ξ) = restrictU C ξ := by
  ext u
  rw [ClassFunction.compHom_apply]
  exact l34ne_restrictU_sigx_apply D C hc ξ u

/-! ## A two-element multiset preserved by an automorphism -/

/-- If an automorphism `σ` of a finite group `U` preserves the sum of two distinct irreducible
characters `α₁ + α₂`, then it permutes the pair `{α₁, α₂}`. -/
theorem l34ne_perm_of_sum {U : Type} [Group U] [Fintype U] [Invertible (Nat.card U : ℂ)]
    (σ : MulAut U) {α₁ α₂ : ClassFunction U ℂ} (hα₁ : IsIrreducibleCharacter α₁)
    (hα₂ : IsIrreducibleCharacter α₂) (hne : α₁ ≠ α₂)
    (hs : ClassFunction.compHom σ.toMonoidHom α₁ + ClassFunction.compHom σ.toMonoidHom α₂
      = α₁ + α₂) :
    (ClassFunction.compHom σ.toMonoidHom α₁ = α₁ ∧ ClassFunction.compHom σ.toMonoidHom α₂ = α₂)
    ∨ (ClassFunction.compHom σ.toMonoidHom α₁ = α₂
      ∧ ClassFunction.compHom σ.toMonoidHom α₂ = α₁) := by
  classical
  set β₁ : ClassFunction U ℂ := ClassFunction.compHom σ.toMonoidHom α₁ with hβ₁
  set β₂ : ClassFunction U ℂ := ClassFunction.compHom σ.toMonoidHom α₂ with hβ₂
  have hβ₁irr : IsIrreducibleCharacter β₁ := hα₁.compHom_of_surjective σ.surjective
  have hβ₂irr : IsIrreducibleCharacter β₂ := hα₂.compHom_of_surjective σ.surjective
  have hinj : ∀ a b : ClassFunction U ℂ,
      ClassFunction.compHom σ.toMonoidHom a = ClassFunction.compHom σ.toMonoidHom b → a = b := by
    intro a b h
    ext v
    obtain ⟨w, rfl⟩ := σ.surjective v
    have := congrArg (fun f : ClassFunction U ℂ => f w) h
    simpa [ClassFunction.compHom_apply] using this
  have hβne : β₁ ≠ β₂ := fun h => hne (hinj _ _ (by rw [← hβ₁, ← hβ₂]; exact h))
  have hinner_eq : ∀ {β γ : ClassFunction U ℂ}, IsIrreducibleCharacter β →
      IsIrreducibleCharacter γ → ClassFunction.inner β γ = 1 → β = γ := by
    intro β γ hβ hγ h
    have hif := irreducibleCharacter_inner_eq_ite (⟨β, hβ⟩ : IrreducibleCharacter U)
      (⟨γ, hγ⟩ : IrreducibleCharacter U)
    by_contra hc
    have hne' : (⟨β, hβ⟩ : IrreducibleCharacter U) ≠ ⟨γ, hγ⟩ := fun hab =>
      hc (Subtype.ext_iff.mp hab)
    rw [ite_eq_right hne'] at hif
    rw [hif] at h
    norm_num at h
  have h01 : ∀ {β : ClassFunction U ℂ}, IsIrreducibleCharacter β →
      ClassFunction.inner β α₁ = 0 ∨ ClassFunction.inner β α₁ = 1 := by
    intro β hβ
    have hif := irreducibleCharacter_inner_eq_ite (⟨β, hβ⟩ : IrreducibleCharacter U)
      (⟨α₁, hα₁⟩ : IrreducibleCharacter U)
    by_cases h : (⟨β, hβ⟩ : IrreducibleCharacter U) = ⟨α₁, hα₁⟩
    · right; rw [hif, ite_eq_left h]
    · left; rw [hif, ite_eq_right h]
  have h02 : ∀ {β : ClassFunction U ℂ}, IsIrreducibleCharacter β →
      ClassFunction.inner β α₂ = 0 ∨ ClassFunction.inner β α₂ = 1 := by
    intro β hβ
    have hif := irreducibleCharacter_inner_eq_ite (⟨β, hβ⟩ : IrreducibleCharacter U)
      (⟨α₂, hα₂⟩ : IrreducibleCharacter U)
    by_cases h : (⟨β, hβ⟩ : IrreducibleCharacter U) = ⟨α₂, hα₂⟩
    · right; rw [hif, ite_eq_left h]
    · left; rw [hif, ite_eq_right h]
  have hcoef₁ : ClassFunction.inner β₁ α₁ + ClassFunction.inner β₁ α₂ = 1 := by
    rw [← ClassFunction.inner_add_right, ← hs, ClassFunction.inner_add_right]
    have h1 : ClassFunction.inner β₁ β₁ = 1 := by
      have hif := irreducibleCharacter_inner_eq_ite (⟨β₁, hβ₁irr⟩ : IrreducibleCharacter U)
        (⟨β₁, hβ₁irr⟩ : IrreducibleCharacter U)
      simpa using hif
    have h2 : ClassFunction.inner β₁ β₂ = 0 := by
      have hif := irreducibleCharacter_inner_eq_ite (⟨β₁, hβ₁irr⟩ : IrreducibleCharacter U)
        (⟨β₂, hβ₂irr⟩ : IrreducibleCharacter U)
      have hne' : (⟨β₁, hβ₁irr⟩ : IrreducibleCharacter U) ≠ ⟨β₂, hβ₂irr⟩ := fun hab =>
        hβne (Subtype.ext_iff.mp hab)
      rw [ite_eq_right hne'] at hif
      simpa using hif
    rw [h1, h2, add_zero]
  have hcoef₂ : ClassFunction.inner β₂ α₁ + ClassFunction.inner β₂ α₂ = 1 := by
    rw [← ClassFunction.inner_add_right, ← hs, ClassFunction.inner_add_right]
    have h1 : ClassFunction.inner β₂ β₁ = 0 := by
      have hif := irreducibleCharacter_inner_eq_ite (⟨β₂, hβ₂irr⟩ : IrreducibleCharacter U)
        (⟨β₁, hβ₁irr⟩ : IrreducibleCharacter U)
      have hne' : (⟨β₂, hβ₂irr⟩ : IrreducibleCharacter U) ≠ ⟨β₁, hβ₁irr⟩ := fun hab =>
        hβne (Subtype.ext_iff.mp hab).symm
      rw [ite_eq_right hne'] at hif
      simpa using hif
    have h2 : ClassFunction.inner β₂ β₂ = 1 := by
      have hif := irreducibleCharacter_inner_eq_ite (⟨β₂, hβ₂irr⟩ : IrreducibleCharacter U)
        (⟨β₂, hβ₂irr⟩ : IrreducibleCharacter U)
      simpa using hif
    rw [h1, h2, zero_add]
  have hval₁ : β₁ = α₁ ∨ β₁ = α₂ := by
    rcases h01 hβ₁irr with h | h <;> rcases h02 hβ₁irr with h' | h'
    · exfalso
      have : (0 : ℂ) = 1 := by rw [← hcoef₁, h, h']; norm_num
      norm_num at this
    · right; exact hinner_eq hβ₁irr hα₂ h'
    · left; exact hinner_eq hβ₁irr hα₁ h
    · exfalso
      have : (2 : ℂ) = 1 := by rw [← hcoef₁, h, h']; norm_num
      norm_num at this
  have hval₂ : β₂ = α₁ ∨ β₂ = α₂ := by
    rcases h01 hβ₂irr with h | h <;> rcases h02 hβ₂irr with h' | h'
    · exfalso
      have : (0 : ℂ) = 1 := by rw [← hcoef₂, h, h']; norm_num
      norm_num at this
    · right; exact hinner_eq hβ₂irr hα₂ h'
    · left; exact hinner_eq hβ₂irr hα₁ h
    · exfalso
      have h2 : (2 : ℂ) = 1 := by rw [← hcoef₂, h, h']; norm_num
      norm_num at h2
  rcases hval₁ with h1 | h1
  · left
    refine ⟨h1, ?_⟩
    have h := hs
    rw [h1] at h
    exact add_left_cancel h
  · right
    refine ⟨h1, ?_⟩
    have h := hs
    rw [h1, add_comm α₁ α₂] at h
    exact add_left_cancel h

/-! ## Index-two subgroups of the Sylow subgroup -/

theorem l34ne_card_S (D : BGData G) : Nat.card ↥(D.S : Subgroup G) = 2 * D.n := by
  obtain ⟨e⟩ := D.dih
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem l34ne_card_S0 (D : BGData G) : Nat.card ↥D.S0 = D.n := (nCases G D).2

theorem l34ne_relIndex_le_two (D : BGData G) (hn4 : D.n = 4) {L : Subgroup G}
    (hL : L ≤ (D.S : Subgroup G)) (hcard : 4 ≤ Nat.card ↥L) :
    L.relIndex (D.S : Subgroup G) ≤ 2 := by
  have h := Subgroup.relIndex_mul_card L (D.S : Subgroup G)
  rw [inf_eq_left.mpr hL, l34ne_card_S D, hn4] at h
  -- `L.relIndex S * |L| = 8`
  have hmul : L.relIndex (D.S : Subgroup G) * Nat.card ↥L = 8 := by
    simpa using h
  have hpos : 0 < Nat.card ↥L := Nat.card_pos
  have hle : L.relIndex (D.S : Subgroup G) * Nat.card ↥L ≤ 2 * Nat.card ↥L := by
    rw [hmul]
    calc (8 : ℕ) = 2 * 4 := by norm_num
      _ ≤ 2 * Nat.card ↥L := Nat.mul_le_mul_left 2 hcard
  exact Nat.le_of_mul_le_mul_right hle hpos

theorem l34ne_card_pair_ge_four (D : BGData G) {g : G}
    (h1 : (1 : G) ≠ D.t) (h2 : (1 : G) ≠ g) (h3 : (1 : G) ≠ g * D.t)
    (h4 : D.t ≠ g) (h5 : D.t ≠ g * D.t) (h6 : g ≠ g * D.t) :
    4 ≤ Nat.card ↥(Subgroup.zpowers g ⊔ Subgroup.zpowers D.t) := by
  have hsub : ({1, D.t, g, g * D.t} : Set G)
      ⊆ ((Subgroup.zpowers g ⊔ Subgroup.zpowers D.t : Subgroup G) : Set G) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy | hy
    · rw [hy]; exact Subgroup.one_mem _
    · rw [hy]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t)
    · rw [hy]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers g)
    · rw [hy]; exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers g))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t))
  have hcard : ({1, D.t, g, g * D.t} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨h1, h2, h3⟩),
      Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨h4, h5⟩),
      Set.ncard_insert_of_notMem (by
          simp only [Set.mem_singleton_iff]
          exact h6),
      Set.ncard_singleton]
  calc (4 : ℕ) = ({1, D.t, g, g * D.t} : Set G).ncard := hcard.symm
    _ ≤ ((Subgroup.zpowers g ⊔ Subgroup.zpowers D.t : Subgroup G) : Set G).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card ↥(Subgroup.zpowers g ⊔ Subgroup.zpowers D.t) := Nat.card_coe_set_eq _

theorem l34ne_four_facts (D : BGData G) {g : G} (hg2 : g * g = 1) (hg1 : g ≠ 1)
    (hgt : g ≠ D.t) (ht1 : D.t ≠ 1) (ht2 : D.t * D.t = 1) :
    (1 : G) ≠ D.t ∧ (1 : G) ≠ g ∧ (1 : G) ≠ g * D.t ∧ D.t ≠ g ∧ D.t ≠ g * D.t
      ∧ g ≠ g * D.t := by
  refine ⟨fun h => ht1 h.symm, fun h => hg1 h.symm, ?_, fun h => hgt h.symm, ?_, ?_⟩
  · intro h
    have h' : g * D.t = 1 := h.symm
    have h'' : g = D.t⁻¹ := mul_eq_one_iff_eq_inv.mp h'
    exact hgt (h''.trans (inv_eq_of_mul_eq_one_right ht2))
  · intro h
    have h' : D.t * D.t⁻¹ = (g * D.t) * D.t⁻¹ := congrArg (fun z => z * D.t⁻¹) h
    rw [mul_inv_cancel, mul_assoc, mul_inv_cancel, mul_one] at h'
    exact hg1 h'.symm
  · intro h
    have h' : g⁻¹ * g = g⁻¹ * (g * D.t) := congrArg (fun z => g⁻¹ * z) h
    rw [inv_mul_cancel, ← mul_assoc, inv_mul_cancel, one_mul] at h'
    exact ht1 h'.symm

theorem l34ne_t_ne_one (D : BGData G) : D.t ≠ 1 := by
  intro h
  have := D.t_order
  rw [h, orderOf_one] at this
  omega

theorem l34ne_L_t1 (D : BGData G) (hn4 : D.n = 4) {u : G} (huU : u ∈ D.U)
    (hu : D.t1 * u = u * D.t1) :
    ∃ L : Subgroup G, L ≤ (D.S : Subgroup G) ∧ L.relIndex (D.S : Subgroup G) ≤ 2 ∧
      (∀ l ∈ L, l * u = u * l) := by
  have hle : (Subgroup.zpowers D.t1 ⊔ Subgroup.zpowers D.t : Subgroup G) ≤ (D.S : Subgroup G) :=
    sup_le (Subgroup.zpowers_le.mpr D.t1_mem) (Subgroup.zpowers_le.mpr (D.S0_le D.t_mem))
  have hg1 : D.t1 ≠ 1 := by
    intro h
    have := D.t1_order
    rw [h, orderOf_one] at this
    omega
  have hgt : D.t1 ≠ D.t := fun h => D.t1_nmem (h ▸ D.t_mem)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := l34ne_four_facts D
    (l34ne_mul_self_eq_one D D.t1_order) hg1 hgt (l34ne_t_ne_one D)
    (l34ne_mul_self_eq_one D D.t_order)
  refine ⟨_, hle, l34ne_relIndex_le_two D hn4 hle ?_, ?_⟩
  · exact l34ne_card_pair_ge_four D h1 h2 h3 h4 h5 h6
  · have hmem : (Subgroup.zpowers D.t1 ⊔ Subgroup.zpowers D.t : Subgroup G)
        ≤ Subgroup.centralizer ({u} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hu.symm
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        have huH : u ∈ D.H := Subgroup.map_subtype_le (Work.GW2.oddCore D.H) huU
        exact (Subgroup.mem_centralizer_iff.mp huH D.t (Set.mem_singleton D.t)).symm
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hmem hl) u (Set.mem_singleton u)).symm

theorem l34ne_L_t2 (D : BGData G) (hn4 : D.n = 4) {u : G} (huU : u ∈ D.U)
    (hu : D.t2 * u = u * D.t2) :
    ∃ L : Subgroup G, L ≤ (D.S : Subgroup G) ∧ L.relIndex (D.S : Subgroup G) ≤ 2 ∧
      (∀ l ∈ L, l * u = u * l) := by
  have hle : (Subgroup.zpowers D.t2 ⊔ Subgroup.zpowers D.t : Subgroup G) ≤ (D.S : Subgroup G) :=
    sup_le (Subgroup.zpowers_le.mpr D.t2_mem) (Subgroup.zpowers_le.mpr (D.S0_le D.t_mem))
  have hg1 : D.t2 ≠ 1 := by
    intro h
    have := D.t2_order
    rw [h, orderOf_one] at this
    omega
  have hgt : D.t2 ≠ D.t := fun h => D.t2_nmem (h ▸ D.t_mem)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := l34ne_four_facts D
    (l34ne_mul_self_eq_one D D.t2_order) hg1 hgt (l34ne_t_ne_one D)
    (l34ne_mul_self_eq_one D D.t_order)
  refine ⟨_, hle, l34ne_relIndex_le_two D hn4 hle ?_, ?_⟩
  · exact l34ne_card_pair_ge_four D h1 h2 h3 h4 h5 h6
  · have hmem : (Subgroup.zpowers D.t2 ⊔ Subgroup.zpowers D.t : Subgroup G)
        ≤ Subgroup.centralizer ({u} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hu.symm
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        have huH : u ∈ D.H := Subgroup.map_subtype_le (Work.GW2.oddCore D.H) huU
        exact (Subgroup.mem_centralizer_iff.mp huH D.t (Set.mem_singleton D.t)).symm
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hmem hl) u (Set.mem_singleton u)).symm

theorem l34ne_L_x (D : BGData G) (hn4 : D.n = 4) {u : G}
    (hu : (D.t1 * D.t2) * u = u * (D.t1 * D.t2)) :
    ∃ L : Subgroup G, L ≤ (D.S : Subgroup G) ∧ L.relIndex (D.S : Subgroup G) ≤ 2 ∧
      (∀ l ∈ L, l * u = u * l) := by
  have hxS : D.t1 * D.t2 ∈ (D.S : Subgroup G) :=
    D.S0_le (by rw [D.gen]; exact Subgroup.mem_zpowers _)
  have hle : Subgroup.zpowers (D.t1 * D.t2) ≤ (D.S : Subgroup G) := Subgroup.zpowers_le.mpr hxS
  refine ⟨_, hle, l34ne_relIndex_le_two D hn4 hle ?_, ?_⟩
  · have hcardL : Nat.card ↥(Subgroup.zpowers (D.t1 * D.t2) : Subgroup G) = 4 := by
      rw [← D.gen, l34ne_card_S0 D, hn4]
    omega
  · intro l hl
    have hgen : (D.t1 * D.t2) ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hu.symm
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.zpowers_le.mpr hgen hl) u (Set.mem_singleton u)).symm

/-! ## Commutation with the fixed subgroups -/

theorem l34ne_comm_sigmaU (D : BGData G) (C : Sec2Ctx G) (hc : Compat D C)
    (c : ↥(fixedSubgroup (sigmaU C))) :
    D.t1 * (((c : ↥C.P.U)) : G) = (((c : ↥C.P.U)) : G) * D.t1 := by
  have h := congrArg (fun x : ↥C.P.U => (x : G))
    (show sigmaU C (c : ↥C.P.U) = (c : ↥C.P.U) from c.2)
  rw [sigmaU_apply_coe, hc.s_eq] at h
  calc D.t1 * (((c : ↥C.P.U)) : G)
      = D.t1 * (((c : ↥C.P.U)) : G) * D.t1⁻¹ * D.t1 := by group
    _ = (((c : ↥C.P.U)) : G) * D.t1 := by rw [h]

theorem l34ne_comm_sigx (D : BGData G) (C : Sec2Ctx G) (hc : Compat D C)
    (c : ↥(fixedSubgroup (l34ne_sigx D C hc))) :
    (D.t1 * D.t2) * (((c : ↥C.P.U)) : G) = (((c : ↥C.P.U)) : G) * (D.t1 * D.t2) := by
  have h := congrArg (fun x : ↥C.P.U => (x : G))
    (show l34ne_sigx D C hc (c : ↥C.P.U) = (c : ↥C.P.U) from c.2)
  rw [l34ne_sigx_apply_coe] at h
  calc (D.t1 * D.t2) * (((c : ↥C.P.U)) : G)
      = (D.t1 * D.t2) * (((c : ↥C.P.U)) : G) * (D.t1 * D.t2)⁻¹ * (D.t1 * D.t2) := by group
    _ = (((c : ↥C.P.U)) : G) * (D.t1 * D.t2) := by rw [h]

theorem l34ne_comm_sig2 (D : BGData G) (C : Sec2Ctx G) (hc : Compat D C)
    (c : ↥(fixedSubgroup (l34ne_sig2 D C hc))) :
    D.t2 * (((c : ↥C.P.U)) : G) = (((c : ↥C.P.U)) : G) * D.t2 := by
  have h := congrArg (fun x : ↥C.P.U => (x : G))
    (show l34ne_sig2 D C hc (c : ↥C.P.U) = (c : ↥C.P.U) from c.2)
  rw [l34ne_sig2_apply_coe] at h
  calc D.t2 * (((c : ↥C.P.U)) : G)
      = D.t2 * (((c : ↥C.P.U)) : G) * D.t2⁻¹ * D.t2 := by group
    _ = (((c : ↥C.P.U)) : G) * D.t2 := by rw [h]

/-! ## The mod-two congruence on `U` from Lemma 2.4 -/

theorem l34ne_cong (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hc : Compat D C)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    {ν ξ : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ bset C f χ) (hξ : ξ ∈ bset C f χ)
    (hne : sconj C ν ≠ ν) (hξν : ξ ≠ ν) (hξνs : ξ ≠ sconj C ν)
    (hbset : bset C f χ = {ν, sconj C ν, ξ})
    {β α₁ α₂ : ClassFunction ↥C.P.U ℂ} (hνβ : restrictU C ν = β)
    (hsνβ : restrictU C (sconj C ν) = β) (hξshape : restrictU C ξ = α₁ + α₂)
    (hα₁irr : IsIrreducibleCharacter α₁) (hα₂irr : IsIrreducibleCharacter α₂)
    (u : ↥C.P.U) :
    AlgIntModTwo (χ ((u : ↥C.P.U) : G)) (α₁ u + α₂ u) := by
  classical
  set uH : ↥C.P.H0 := ⟨(u : G), C.P.U_le_H0 u.2⟩ with huH
  have hsum := (lemma24 C f hf χ hχ).2.2 uH (by simpa [huH] using u.2)
  have hnot1 : ν ∉ ({sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hne h.symm, fun h => hξν h.symm⟩
  have hnot2 : sconj C ν ∉ ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    simp only [Set.mem_singleton_iff]
    exact fun h => hξνs h.symm
  have hsplit : (∑ᶠ η ∈ bset C f χ, η uH) = ν uH + (sconj C ν) uH + ξ uH := by
    rw [hbset, finsum_mem_insert _ hnot1 (Set.toFinite _),
      finsum_mem_insert _ hnot2 (Set.toFinite _), finsum_mem_singleton]
    ring
  rw [hsplit] at hsum
  have h1 : ν uH = β u := by
    rw [← restrictU_apply C ν u, hνβ]
  have h2 : (sconj C ν) uH = β u := by
    rw [← restrictU_apply C (sconj C ν) u, hsνβ]
  have h3 : ξ uH = α₁ u + α₂ u := by
    rw [← restrictU_apply C ξ u, hξshape, ClassFunction.add_apply]
  rw [h1, h2, h3] at hsum
  have hβint : IsIntegral ℤ (β u) := by
    rw [← h1]
    exact isIntegral_apply_of_isIrreducibleCharacter hν.1 uH
  have hαint : IsIntegral ℤ (α₁ u + α₂ u) :=
    (isIntegral_apply_of_isIrreducibleCharacter hα₁irr u).add
      (isIntegral_apply_of_isIrreducibleCharacter hα₂irr u)
  -- derive integrality of α₁ u, α₂ u from Lemma 2.4? -- not available; instead use the shapes
  have hdrop : AlgIntModTwo (β u + β u + (α₁ u + α₂ u)) (α₁ u + α₂ u) := by
    have h0 : AlgIntModTwo (β u + β u) 0 := by
      have : β u + β u = 2 * β u := by ring
      rw [this]
      exact AlgIntModTwo.mul_two hβint
    have := AlgIntModTwo.add h0
      (AlgIntModTwo.refl (α₁ u + α₂ u) hαint)
    simpa using this
  exact hsum.trans hdrop

/-! ## The main theorem -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem l34ne_main {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D →
    ∀ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, Work.GW2.C16.IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, Work.BG.IsPmIrr χ →
    ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ≠ ν →
      (Work.BG.sconj C ν ∉ Work.BG.lamOrbit C ν ∨ (Work.BG.lamOrbit C ν).ncard = D.n) →
      (Work.BG.lamOrbit C ν).ncard = 4 →
      Work.BG.sconj C '' Work.BG.lamOrbit C ν = Work.BG.lamOrbit C ν →
      ∀ ξ ∈ Work.GW2.C16.bset C f χ, ξ ≠ ν → ξ ≠ Work.BG.sconj C ν →
      Work.BG.sconj C ξ = ξ → (Work.BG.lamOrbit C ξ).ncard ≠ 4 → False := by
  intro hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv ξ hξ hξν hξνs hξfix hξne4
  haveI : Fintype ↥C.P.U := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥C.P.U : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have huniq : D.n = 4 := l34ne_n_eq_four D C hdisj hinv h4
  have hbset : bset C f χ = {ν, sconj C ν, ξ} :=
    l34ne_bset_eq D C hDC hS3 f hf χ hχ hν hne hξ hξν hξνs
  obtain ⟨⟨β, hβirr, hνβ, hsνβ⟩, ⟨α₁, α₂, hα₁irr, hα₂irr, hαne, hαdeg, hξshape⟩, hξ2⟩ :=
    l34ne_restrict_shape D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv huniq ξ hξ hξν hξνs
      hξfix hξne4
  -- `4 ∣ χ 1`
  have hξdeg : ∃ m : ℤ, ξ 1 = (2 : ℂ) * (m : ℂ) ∧ Odd m := by
    obtain ⟨n₁, hn₁odd, hn₁⟩ := exists_odd_nat_degree (odd_card_U_of_compat hDC) hα₁irr
    refine ⟨(n₁ : ℤ), ?_, by exact_mod_cast hn₁odd⟩
    have h1 : restrictU C ξ (1 : ↥C.P.U) = ξ 1 := by
      rw [restrictU_apply]
      exact congrArg ξ (Subtype.ext (by simp))
    have h' : ξ 1 = α₁ 1 + α₂ 1 := by
      rw [← h1, hξshape, ClassFunction.add_apply]
    have hα₂ : α₂ 1 = (n₁ : ℂ) := by rw [← hαdeg]; exact hn₁
    rw [h', hn₁, hα₂]
    push_cast
    ring
  have h4dvd : ∃ k : ℤ, χ 1 = (4 : ℂ) * (k : ℂ) :=
    l34ne_deg_mod_four D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv huniq ξ hξ hξν hξνs
      hξfix hξne4 hbset hξdeg
  -- the two stabilities
  have hs1 : ClassFunction.compHom (sigmaU C).toMonoidHom α₁
      + ClassFunction.compHom (sigmaU C).toMonoidHom α₂ = α₁ + α₂ := by
    have h := l34ne_restrictU_sigmaU C hξfix
    rw [hξshape, ClassFunction.compHom_add] at h
    exact h
  have hsx : ClassFunction.compHom (l34ne_sigx D C hDC).toMonoidHom α₁
      + ClassFunction.compHom (l34ne_sigx D C hDC).toMonoidHom α₂ = α₁ + α₂ := by
    have h := l34ne_restrictU_sigx D C hDC ξ
    rw [hξshape, ClassFunction.compHom_add] at h
    exact h
  have hperm1 := l34ne_perm_of_sum (sigmaU C) hα₁irr hα₂irr hαne hs1
  have hpermx := l34ne_perm_of_sum (l34ne_sigx D C hDC) hα₁irr hα₂irr hαne hsx
  -- the common contradiction step
  have contra : ∀ (σ : MulAut ↥C.P.U), σ * σ = 1 →
      ClassFunction.compHom σ.toMonoidHom α₁ = α₁ →
      ClassFunction.compHom σ.toMonoidHom α₂ = α₂ →
      (∀ c : ↥(fixedSubgroup σ), ∃ L : Subgroup G, L ≤ (D.S : Subgroup G) ∧
        L.relIndex (D.S : Subgroup G) ≤ 2 ∧
        (∀ l ∈ L, l * (((c : ↥C.P.U)) : G) = (((c : ↥C.P.U)) : G) * l)) →
      False := by
    intro σ hσ h1 h2 hL
    haveI : Fintype ↥(fixedSubgroup σ) := Fintype.ofFinite _
    haveI : Invertible (Nat.card ↥(fixedSubgroup σ) : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    refine l34ne_glauberman_contra (odd_card_U_of_compat hDC) σ hσ hα₁irr hα₂irr ?_ ?_ hαne ?_
    · intro u
      have := congrArg (fun f : ClassFunction ↥C.P.U ℂ => f u) h1
      simpa [ClassFunction.compHom_apply] using this
    · intro u
      have := congrArg (fun f : ClassFunction ↥C.P.U ℂ => f u) h2
      simpa [ClassFunction.compHom_apply] using this
    · intro c
      have hc0 : AlgIntModTwo (χ (((c : ↥C.P.U)) : G)) 0 :=
        l34ne_chi_even (D.S) hχ h4dvd (hL c)
      have hc1 : AlgIntModTwo (χ (((c : ↥C.P.U)) : G))
          (α₁ (c : ↥C.P.U) + α₂ (c : ↥C.P.U)) :=
        l34ne_cong D C hDC f hf χ hχ hν hξ hne hξν hξνs hbset hνβ hsνβ hξshape
          hα₁irr hα₂irr (c : ↥C.P.U)
      exact (hc0.symm.trans hc1).symm
  rcases hperm1 with ⟨h11, h12⟩ | ⟨h11, h12⟩
  · exact contra (sigmaU C) (sigmaU_mul_self C) h11 h12 (fun c =>
      l34ne_L_t1 D huniq (by simpa only [hDC.U_eq] using (c : ↥C.P.U).2)
        (l34ne_comm_sigmaU D C hDC c))
  · rcases hpermx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
    · exact contra (l34ne_sigx D C hDC) (l34ne_sigx_mul_self D C hDC hS3) hx1 hx2 (fun c =>
        l34ne_L_x D huniq (l34ne_comm_sigx D C hDC c))
    · have h21 : ClassFunction.compHom (l34ne_sig2 D C hDC).toMonoidHom α₁ = α₁ := by
        rw [l34ne_sig2_eq D C hDC, l34ne_compHom_mul, h11, hx2]
      have h22 : ClassFunction.compHom (l34ne_sig2 D C hDC).toMonoidHom α₂ = α₂ := by
        rw [l34ne_sig2_eq D C hDC, l34ne_compHom_mul, h12, hx1]
      exact contra (l34ne_sig2 D C hDC) (l34ne_sig2_mul_self D C hDC) h21 h22 (fun c =>
        l34ne_L_t2 D huniq (by simpa only [hDC.U_eq] using (c : ↥C.P.U).2)
          (l34ne_comm_sig2 D C hDC c))

end Work.BG