import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.CharBridge
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.S_le_H
import Submission.Work.BG.isFourGroup_closure_pair
import Submission.Work.BG.nCases

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-! ## 1. Conjugation of `U = O_{2'}(H)` by elements of `H` -/

open Work.GW2 Work.GW2.C16 in
theorem c3deEF_U_normal (D : BGData G) : (D.U.subgroupOf D.H).Normal := by
  have hU'eq : D.U.subgroupOf D.H = oddCore ↥D.H := by
    rw [show D.U = oddCoreIn D.H from rfl, oddCoreIn, Subgroup.subgroupOf]
    exact Subgroup.comap_map_eq_self_of_injective D.H.subtype_injective _
  rw [hU'eq]
  exact oddCore_normal ↥D.H

open Work.GW2 Work.GW2.C16 in
theorem c3deEF_conj_mem_U {D : BGData G} {C : Sec2Ctx G} (hc : Compat D C)
    {g : G} (hg : g ∈ C.P.H) {u : G} (hu : u ∈ C.P.U) : g * u * g⁻¹ ∈ C.P.U := by
  have hUDH : D.U ≤ D.H := Subgroup.map_subtype_le (oddCore ↥D.H)
  rw [hc.U_eq, hc.H_eq] at *
  have hmem := (c3deEF_U_normal D).conj_mem
    (⟨u, hUDH hu⟩ : ↥D.H) (Subgroup.mem_subgroupOf.mpr hu) (⟨g, hg⟩ : ↥D.H)
  exact Subgroup.mem_subgroupOf.mp hmem

open Work.GW2 Work.GW2.C16 in
/-- Conjugation by `g ∈ ↥C.P.H` as an automorphism of `↥C.P.U`. -/
noncomputable def c3deEF_conjAutU {D : BGData G} {C : Sec2Ctx G} (hc : Compat D C)
    (g : ↥C.P.H) : MulAut ↥C.P.U where
  toFun u := ⟨(g : G) * (u : G) * (g : G)⁻¹, c3deEF_conj_mem_U hc g.2 u.2⟩
  invFun u := ⟨(g : G)⁻¹ * (u : G) * (g : G), by
    have h := c3deEF_conj_mem_U hc (C.P.H.inv_mem g.2) u.2
    simp only [inv_inv] at h
    exact h⟩
  left_inv u := by
    apply Subtype.ext
    show (g : G)⁻¹ * ((g : G) * (u : G) * (g : G)⁻¹) * (g : G) = (u : G)
    group
  right_inv u := by
    apply Subtype.ext
    show (g : G) * ((g : G)⁻¹ * (u : G) * (g : G)) * (g : G)⁻¹ = (u : G)
    group
  map_mul' u v := by
    apply Subtype.ext
    show (g : G) * ((u : G) * (v : G)) * (g : G)⁻¹
        = ((g : G) * (u : G) * (g : G)⁻¹) * ((g : G) * (v : G) * (g : G)⁻¹)
    group

open Work.GW2 Work.GW2.C16 in
@[simp] theorem c3deEF_conjAutU_apply_coe {D : BGData G} {C : Sec2Ctx G} (hc : Compat D C)
    (g : ↥C.P.H) (u : ↥C.P.U) :
    (((c3deEF_conjAutU hc g) u : ↥C.P.U) : G) = (g : G) * (u : G) * (g : G)⁻¹ := rfl

open Work.GW2 Work.GW2.C16 in
theorem c3deEF_conjAutU_mul {D : BGData G} {C : Sec2Ctx G} (hc : Compat D C)
    (g h : ↥C.P.H) :
    c3deEF_conjAutU hc (g * h) = c3deEF_conjAutU hc g * c3deEF_conjAutU hc h := by
  refine MulEquiv.ext fun u => Subtype.ext ?_
  show (g : G) * (h : G) * (u : G) * ((g : G) * (h : G))⁻¹
      = (g : G) * ((h : G) * (u : G) * (h : G)⁻¹) * (g : G)⁻¹
  group

open Work.GW2 Work.GW2.C16 in
theorem c3deEF_conjAutU_one {D : BGData G} {C : Sec2Ctx G} (hc : Compat D C) :
    c3deEF_conjAutU hc (1 : ↥C.P.H) = 1 := by
  refine MulEquiv.ext fun u => Subtype.ext ?_
  show (1 : G) * (u : G) * (1 : G)⁻¹ = (u : G)
  group

open Work.GW2 Work.GW2.C16 in
theorem c3deEF_conjAutU_sq {D : BGData G} {C : Sec2Ctx G} (hc : Compat D C)
    (g : ↥C.P.H) (hg : ((g : G)) ^ 2 = 1) :
    c3deEF_conjAutU hc g * c3deEF_conjAutU hc g = 1 := by
  rw [← c3deEF_conjAutU_mul]
  have h : g * g = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hg
  rw [h, c3deEF_conjAutU_one]

open Work.GW2 Work.GW2.C16 in
theorem c3deEF_conjAutU_central {D : BGData G} {C : Sec2Ctx G} (hc : Compat D C)
    (g : ↥C.P.H) (hg : ∀ u : ↥C.P.U, (g : G) * (u : G) = (u : G) * (g : G)) :
    c3deEF_conjAutU hc g = 1 := by
  refine MulEquiv.ext fun u => Subtype.ext ?_
  show (g : G) * (u : G) * (g : G)⁻¹ = (u : G)
  rw [hg u]
  group

/-! ## 2. `(t₁ t₂)² = t` -/

open Work.GW2 Work.GW2.C16 in
theorem c3deEF_sq_t1t2 {D : BGData G} (hD4 : D.n = 4) : (D.t1 * D.t2) ^ 2 = D.t := by
  haveI : IsCyclic ↥D.S0 := D.S0_cyclic
  have hcardS0 : Nat.card ↥D.S0 = 4 := by rw [(Work.BG.nCases G D).2, hD4]
  have horder : orderOf (D.t1 * D.t2) = 4 := by
    have h : Nat.card (Subgroup.zpowers (D.t1 * D.t2)) = 4 := by
      rw [← D.gen]; exact hcardS0
    rwa [Nat.card_zpowers] at h
  have hmem : (D.t1 * D.t2) ^ 2 ∈ D.S0 := by
    rw [D.gen]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
  have hne1 : (D.t1 * D.t2) ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf (D.t1 * D.t2) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [horder] at hdvd
    exact absurd hdvd (by decide)
  have hpow : ((D.t1 * D.t2) ^ 2) ^ 2 = 1 := by
    have h4 : (D.t1 * D.t2) ^ 4 = 1 := by
      have := pow_orderOf_eq_one (D.t1 * D.t2)
      rwa [horder] at this
    calc ((D.t1 * D.t2) ^ 2) ^ 2 = (D.t1 * D.t2) ^ (2 * 2) := by rw [pow_mul]
      _ = (D.t1 * D.t2) ^ 4 := by norm_num
      _ = 1 := h4
  have ha : orderOf (⟨(D.t1 * D.t2) ^ 2, hmem⟩ : ↥D.S0) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hpow hne1
  have hb : orderOf (⟨D.t, D.t_mem⟩ : ↥D.S0) = 2 := by
    rw [Subgroup.orderOf_mk]; exact D.t_order
  exact congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic ha hb)

/-! ## 3. An automorphism acting on a two-term sum of irreducibles -/

/-- If `α₁ + α₂` (`αᵢ ∈ Irr U`, `U` finite) is invariant under an automorphism `σ` of `U`, then
`σ` either fixes both `α₁, α₂` or interchanges them. -/
theorem c3deEF_fixes_or_swaps {U : Type} [Group U] [Fintype U] [Invertible (Nat.card U : ℂ)]
    (σ : MulAut U) {α₁ α₂ : ClassFunction U ℂ} (hα₁ : IsIrreducibleCharacter α₁)
    (hα₂ : IsIrreducibleCharacter α₂) (hne : α₁ ≠ α₂)
    (hsum : ∀ u : U, α₁ (σ u) + α₂ (σ u) = α₁ u + α₂ u) :
    ((∀ u, α₁ (σ u) = α₁ u) ∧ (∀ u, α₂ (σ u) = α₂ u)) ∨
      ((∀ u, α₁ (σ u) = α₂ u) ∧ (∀ u, α₂ (σ u) = α₁ u)) := by
  classical
  have f1irr : IsIrreducibleCharacter (ClassFunction.compHom (σ : U →* U) α₁) :=
    IsIrreducibleCharacter.compHom_of_surjective σ.surjective hα₁
  have f2irr : IsIrreducibleCharacter (ClassFunction.compHom (σ : U →* U) α₂) :=
    IsIrreducibleCharacter.compHom_of_surjective σ.surjective hα₂
  have happ1 : ∀ u : U, ClassFunction.compHom (σ : U →* U) α₁ u = α₁ (σ u) :=
    fun u => ClassFunction.compHom_apply (σ : U →* U) α₁ u
  have happ2 : ∀ u : U, ClassFunction.compHom (σ : U →* U) α₂ u = α₂ (σ u) :=
    fun u => ClassFunction.compHom_apply (σ : U →* U) α₂ u
  have hsum' : ClassFunction.compHom (σ : U →* U) α₁ + ClassFunction.compHom (σ : U →* U) α₂
      = α₁ + α₂ := by
    ext u
    simp only [ClassFunction.add_apply, happ1 u, happ2 u]
    exact hsum u
  have ha2 : (⟨α₂, hα₂⟩ : IrreducibleCharacter U) ≠ (⟨α₁, hα₁⟩ : IrreducibleCharacter U) := by
    intro hh
    exact hne (Subtype.ext_iff.mp hh).symm
  have hinner : (if (⟨ClassFunction.compHom (σ : U →* U) α₁, f1irr⟩ : IrreducibleCharacter U)
          = ⟨α₁, hα₁⟩ then (1 : ℂ) else 0)
      + (if (⟨ClassFunction.compHom (σ : U →* U) α₂, f2irr⟩ : IrreducibleCharacter U)
          = ⟨α₁, hα₁⟩ then (1 : ℂ) else 0) = 1 := by
    have h := congrArg (fun cf : ClassFunction U ℂ => ClassFunction.inner cf α₁) hsum'
    rw [ClassFunction.inner_add_left, ClassFunction.inner_add_left] at h
    rw [irreducibleCharacter_inner_eq_ite
          (⟨ClassFunction.compHom (σ : U →* U) α₁, f1irr⟩ : IrreducibleCharacter U)
          (⟨α₁, hα₁⟩ : IrreducibleCharacter U),
        irreducibleCharacter_inner_eq_ite
          (⟨ClassFunction.compHom (σ : U →* U) α₂, f2irr⟩ : IrreducibleCharacter U)
          (⟨α₁, hα₁⟩ : IrreducibleCharacter U),
        irreducibleCharacter_inner_eq_ite
          (⟨α₁, hα₁⟩ : IrreducibleCharacter U) (⟨α₁, hα₁⟩ : IrreducibleCharacter U),
        irreducibleCharacter_inner_eq_ite
          (⟨α₂, hα₂⟩ : IrreducibleCharacter U) (⟨α₁, hα₁⟩ : IrreducibleCharacter U)] at h
    rw [if_pos rfl, if_neg ha2, add_zero] at h
    exact h
  by_cases h1 : (⟨ClassFunction.compHom (σ : U →* U) α₁, f1irr⟩ : IrreducibleCharacter U)
      = ⟨α₁, hα₁⟩
  · left
    have e1 : ∀ u, α₁ (σ u) = α₁ u := by
      intro u
      have h := congrArg (fun x : IrreducibleCharacter U => (x : ClassFunction U ℂ) u) h1
      rw [happ1 u] at h; exact h
    refine ⟨e1, ?_⟩
    intro u
    have hu := hsum u
    rw [e1 u] at hu
    exact add_left_cancel hu
  · right
    have h2 : (⟨ClassFunction.compHom (σ : U →* U) α₂, f2irr⟩ : IrreducibleCharacter U)
        = ⟨α₁, hα₁⟩ := by
      by_contra h2c
      have h := hinner
      rw [if_neg h1, if_neg h2c] at h
      simp only [zero_add] at h
      exact zero_ne_one h
    have e2 : ∀ u, α₂ (σ u) = α₁ u := by
      intro u
      have h := congrArg (fun x : IrreducibleCharacter U => (x : ClassFunction U ℂ) u) h2
      rw [happ2 u] at h; exact h
    refine ⟨?_, e2⟩
    intro u
    have hu := hsum u
    rw [e2 u, add_comm (α₁ (σ u)) (α₁ u)] at hu
    exact add_left_cancel hu

/-! ## 4. A little commutation lemma for `⟨a, b⟩` -/

omit [Finite G] in
theorem c3deEF_closure_comm {u a b : G} (ha : a * u = u * a) (hb : b * u = u * b)
    {l : G} (hl : l ∈ Subgroup.closure ({a, b} : Set G)) : l * u = u * l := by
  have hinv : ∀ x : G, x * u = u * x → x⁻¹ * u = u * x⁻¹ := by
    intro x hx
    calc x⁻¹ * u = x⁻¹ * (u * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * u) * x⁻¹ := by rw [← hx]
      _ = u * x⁻¹ := by group
  exact Subgroup.closure_induction (p := fun l _ => l * u = u * l)
    (fun x hx => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb)
    (by rw [one_mul, mul_one])
    (fun x y _ _ hx hy => by rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc])
    (fun x _ hx => hinv x hx) hl

/-! ## 5. The main theorem -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- In the exceptional configuration (`D.n = 4`, `ξ` irreducible and `s`-fixed with
`ξ|_U = α₁ + α₂`, `α₁ ≠ α₂`, `|Λξ| = 2`) there is an involutive automorphism `σ` of `U`
fixing `α₁` and `α₂` pointwise, together with a subgroup `L ≤ S` of index at most `2` that
centralizes the fixed points of `σ` (in `G`). -/
theorem c3deExistsFixing {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype ↥(C.P.U)] [Invertible (Nat.card ↥(C.P.U) : ℂ)]
    (hDC : Work.GW2.C16.Compat D C) (hS3 : Work.GW2.C16.Sec3Hyp D) (hD4 : D.n = 4)
    {ξ : ClassFunction ↥C.P.H0 ℂ} (hξ : IsIrreducibleCharacter ξ)
    (hξs : Work.BG.sconj C ξ = ξ)
    {α₁ α₂ : ClassFunction ↥(C.P.U) ℂ} (hα₁ : IsIrreducibleCharacter α₁)
    (hα₂ : IsIrreducibleCharacter α₂) (hαne : α₁ ≠ α₂)
    (hξα : restrictU C ξ = α₁ + α₂)
    (hcardξ : (Work.BG.lamOrbit C ξ).ncard = 2) :
    ∃ (σ : MulAut ↥(C.P.U)) (L : Subgroup G),
      σ * σ = 1 ∧ L ≤ (D.S : Subgroup G) ∧ L.relIndex (D.S : Subgroup G) ≤ 2 ∧
      (∀ u : ↥(C.P.U), α₁ (σ u) = α₁ u) ∧ (∀ u : ↥(C.P.U), α₂ (σ u) = α₂ u) ∧
      (∀ u : ↥(C.P.U), σ u = u → ∀ l ∈ L, l * (u : G) = (u : G) * l) := by
  classical
  -- ## Basic memberships in `C.P.H = D.H`
  have hsH : (D.S : Subgroup G) ≤ D.H := S_le_H D
  have ht1H : D.t1 ∈ C.P.H := by rw [hDC.H_eq]; exact hsH D.t1_mem
  have ht2H : D.t2 ∈ C.P.H := by rw [hDC.H_eq]; exact hsH D.t2_mem
  have ht12H : D.t1 * D.t2 ∈ C.P.H := mul_mem ht1H ht2H
  have htH : D.t ∈ C.P.H := by rw [hDC.H_eq]; exact hsH (D.S0_le D.t_mem)
  let g12 : ↥C.P.H := ⟨D.t1 * D.t2, ht12H⟩
  let g2 : ↥C.P.H := ⟨D.t2, ht2H⟩
  -- ## Cardinalities
  have hcardS : Nat.card (D.S : Subgroup G) = 2 * D.n := by
    obtain ⟨e⟩ := D.dih
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hcardS8 : Nat.card (D.S : Subgroup G) = 8 := by rw [hcardS, hD4]
  -- ## The specific conjugations
  have hσeq : c3deEF_conjAutU hDC C.s = sigmaU C := by
    refine MulEquiv.ext fun u => Subtype.ext ?_
    rfl
  have hτrel : c3deEF_conjAutU hDC g12
      = sigmaU C * c3deEF_conjAutU hDC g2 := by
    rw [show g12 = C.s * g2 from by
          apply Subtype.ext
          show D.t1 * D.t2 = (C.s : G) * D.t2
          rw [hDC.s_eq],
        c3deEF_conjAutU_mul, hσeq]
  have hτ2rel : c3deEF_conjAutU hDC g2
      = sigmaU C * c3deEF_conjAutU hDC g12 := by
    have h2 : sigmaU C * c3deEF_conjAutU hDC g12
        = sigmaU C * (sigmaU C * c3deEF_conjAutU hDC g2) := by rw [hτrel]
    rw [h2, ← mul_assoc, sigmaU_mul_self C, one_mul]
  -- ## The three involutions
  have hτ2sq : c3deEF_conjAutU hDC g2 * c3deEF_conjAutU hDC g2 = 1 := by
    refine c3deEF_conjAutU_sq hDC _ ?_
    show D.t2 ^ 2 = 1
    simpa [D.t2_order] using pow_orderOf_eq_one D.t2
  have hτtsq : c3deEF_conjAutU hDC g12
      * c3deEF_conjAutU hDC g12 = 1 := by
    rw [← c3deEF_conjAutU_mul]
    have hsq : (⟨D.t1 * D.t2, ht12H⟩ : ↥C.P.H) * ⟨D.t1 * D.t2, ht12H⟩ = ⟨D.t, htH⟩ := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, pow_two] using c3deEF_sq_t1t2 hD4
    rw [hsq]
    refine c3deEF_conjAutU_central hDC _ ?_
    intro u
    have hcomm : (u : G) * D.t = D.t * (u : G) := by
      have := C.t_comm_H (u : G) (C.P.H0_le_H (C.P.U_le_H0 u.2))
      rwa [hDC.t_eq] at this
    exact hcomm.symm
  -- ## `s`-invariance of the restriction to `U`
  have hres1 : ∀ u : ↥C.P.U, (restrictU C ξ) (sigmaU C u) = (restrictU C ξ) u := by
    intro u
    have hconj : ξ (conjMulEquiv C.P C.s ⟨(u : G), C.P.U_le_H0 u.2⟩)
        = ξ ⟨(u : G), C.P.U_le_H0 u.2⟩ := by
      have h := congrArg (fun f : ClassFunction ↥C.P.H0 ℂ =>
        f ⟨(u : G), C.P.U_le_H0 u.2⟩) hξs
      rw [sconj, conjByH_apply] at h
      exact h
    have hsub : (⟨((sigmaU C u : ↥C.P.U) : G), C.P.U_le_H0 (sigmaU C u).2⟩ : ↥C.P.H0)
        = conjMulEquiv C.P C.s ⟨(u : G), C.P.U_le_H0 u.2⟩ := by
      apply Subtype.ext
      rw [sigmaU_apply_coe, conjMulEquiv_apply]
    rw [restrictU_apply, restrictU_apply, hsub, hconj]
  have hsum1 : ∀ u : ↥C.P.U, α₁ (sigmaU C u) + α₂ (sigmaU C u) = α₁ u + α₂ u := by
    intro u
    have h := hres1 u
    rw [hξα] at h
    simpa only [ClassFunction.add_apply] using h
  -- ## invariance of the restriction to `U` under `conj (t₁ t₂)`
  have ht12H0 : D.t1 * D.t2 ∈ C.P.H0 := by
    rw [hDC.H0_eq]
    show D.t1 * D.t2 ∈ D.U ⊔ D.S0
    exact (le_sup_right : D.S0 ≤ D.U ⊔ D.S0) (by rw [D.gen]; exact Subgroup.mem_zpowers _)
  let h12 : ↥C.P.H0 := ⟨D.t1 * D.t2, ht12H0⟩
  have hresτ : ∀ u : ↥C.P.U,
      (restrictU C ξ) (c3deEF_conjAutU hDC g12 u) = (restrictU C ξ) u := by
    intro u
    let w : ↥C.P.H0 := ⟨((c3deEF_conjAutU hDC g12 u : ↥C.P.U) : G),
        C.P.U_le_H0 (c3deEF_conjAutU hDC g12 u).2⟩
    have hkey : w = h12 * ⟨(u : G), C.P.U_le_H0 u.2⟩ * h12⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [c3deEF_conjAutU_apply_coe]
    calc (restrictU C ξ) (c3deEF_conjAutU hDC g12 u)
        = ξ w := restrictU_apply C ξ _
      _ = ξ (h12 * ⟨(u : G), C.P.U_le_H0 u.2⟩ * h12⁻¹) := by rw [hkey]
      _ = ξ ⟨(u : G), C.P.U_le_H0 u.2⟩ :=
          ClassFunction.conj_eq ξ ⟨(u : G), C.P.U_le_H0 u.2⟩ h12
      _ = (restrictU C ξ) u := (restrictU_apply C ξ u).symm
  have hsumτ : ∀ u : ↥C.P.U,
      α₁ (c3deEF_conjAutU hDC g12 u)
        + α₂ (c3deEF_conjAutU hDC g12 u) = α₁ u + α₂ u := by
    intro u
    have h := hresτ u
    rw [hξα] at h
    simpa only [ClassFunction.add_apply] using h
  -- ## the behaviour of `α₁` under the two involutions
  have hset1 : (∀ u, α₁ (sigmaU C u) = α₁ u) ∨ (∀ u, α₁ (sigmaU C u) = α₂ u) := by
    rcases c3deEF_fixes_or_swaps (sigmaU C) hα₁ hα₂ hαne hsum1 with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have hsetτ : (∀ u, α₁ (c3deEF_conjAutU hDC g12 u) = α₁ u)
      ∨ (∀ u, α₁ (c3deEF_conjAutU hDC g12 u) = α₂ u) := by
    rcases c3deEF_fixes_or_swaps (c3deEF_conjAutU hDC g12) hα₁ hα₂ hαne hsumτ
      with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  -- ## Case split
  rcases hset1 with hA | hB
  · -- ### Case A: `σ = conj s` fixes `α₁, α₂`; `L = ⟨t, s⟩`
    set L : Subgroup G := Subgroup.closure ({(C.t : G), (C.s : G)} : Set G) with hLdef
    have hcardL : Nat.card ↥L = 4 := by
      rw [hLdef]
      exact (isFourGroup_closure_pair (a := (C.t : G)) (b := (C.s : G))
        (by simpa using congrArg (fun x : ↥C.P.H0 => (x : G)) C.t_sq)
        (by simpa using congrArg (fun x : ↥C.P.H => (x : G)) C.s_sq)
        (C.t_comm_H (C.s : G) C.s.2).symm
        (by intro h; exact C.t_not_mem_U (by rw [h]; exact C.P.U.one_mem))
        (by intro h; exact C.s_not_mem_H0 (by rw [h]; exact C.P.H0.one_mem))
        (by intro h; exact C.s_not_mem_H0 (by rw [← h]; exact C.t.2))).1
    have hLle : L ≤ (D.S : Subgroup G) := by
      rw [hLdef, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · rw [hDC.t_eq]; exact D.S0_le D.t_mem
      · rw [hDC.s_eq]; exact D.t1_mem
    have hrel : L.relIndex (D.S : Subgroup G) ≤ 2 := by
      have h := Subgroup.relIndex_mul_card L (D.S : Subgroup G)
      rw [inf_eq_left.mpr hLle, hcardL, hcardS8] at h
      omega
    refine ⟨sigmaU C, L, sigmaU_mul_self C, hLle, hrel, hA, ?_, ?_⟩
    · intro u
      have hu := hsum1 u
      rw [hA u] at hu
      exact add_left_cancel hu
    · intro u hu l hl
      rw [hLdef] at hl
      have hu' : (C.s : G) * (u : G) * (C.s : G)⁻¹ = (u : G) := by
        have h := congrArg (fun x : ↥C.P.U => (x : G)) hu
        rwa [sigmaU_apply_coe] at h
      have hcomm_s : (C.s : G) * (u : G) = (u : G) * (C.s : G) := by
        calc (C.s : G) * (u : G) = (C.s : G) * (u : G) * (C.s : G)⁻¹ * (C.s : G) := by group
          _ = (u : G) * (C.s : G) := by rw [hu']
      have hcomm_t : (C.t : G) * (u : G) = (u : G) * (C.t : G) :=
        (C.t_comm_H (u : G) (C.P.H0_le_H (C.P.U_le_H0 u.2))).symm
      exact c3deEF_closure_comm hcomm_t hcomm_s hl
  · -- ### Case B: `σ = conj s` swaps `α₁, α₂`
    have hB2 : ∀ u, α₂ (sigmaU C u) = α₁ u := by
      intro u
      have hu := hsum1 u
      rw [hB u, add_comm (α₂ u) (α₂ (sigmaU C u))] at hu
      exact add_right_cancel hu
    -- relations with `τ₂ = conj t₂`
    have hτ2A : ∀ u, α₂ (c3deEF_conjAutU hDC g12 u)
        = α₁ (c3deEF_conjAutU hDC g2 u) := by
      intro u
      have h : c3deEF_conjAutU hDC g12 u
          = sigmaU C (c3deEF_conjAutU hDC g2 u) := by
        rw [hτrel]
        exact MulAut.mul_apply _ _ _ _
      rw [h]; exact hB2 _
    have hAτ2 : ∀ u, α₁ (c3deEF_conjAutU hDC g12 u)
        = α₂ (c3deEF_conjAutU hDC g2 u) := by
      intro u
      have h : c3deEF_conjAutU hDC g12 u
          = sigmaU C (c3deEF_conjAutU hDC g2 u) := by
        rw [hτrel]
        exact MulAut.mul_apply _ _ _ _
      rw [h]; exact hB _
    by_cases hC : ∀ u, α₁ (c3deEF_conjAutU hDC g2 u) = α₁ u
    · -- ### Case B1: `σ = conj t₂`; `L = ⟨t, t₂⟩`
      have hτ2fix : ∀ u, α₂ (c3deEF_conjAutU hDC g2 u) = α₂ u := by
        intro u
        have hu := hsumτ u
        rw [hAτ2 u] at hu
        rw [hτ2A u, hC u] at hu
        rw [add_comm (α₂ (c3deEF_conjAutU hDC g2 u)) (α₁ u)] at hu
        exact add_left_cancel hu
      set L : Subgroup G := Subgroup.closure ({(D.t : G), D.t2} : Set G) with hLdef
      have hcardL : Nat.card ↥L = 4 := by
        rw [hLdef]
        exact (isFourGroup_closure_pair (a := D.t) (b := D.t2)
          (by simpa [D.t_order] using pow_orderOf_eq_one D.t)
          (by simpa [D.t2_order] using pow_orderOf_eq_one D.t2)
          ((Subgroup.mem_centralizer_singleton_iff.mp (hsH D.t2_mem)).symm)
          (by intro h; have h2 := D.t_order; rw [h, orderOf_one] at h2; exact absurd h2 (by norm_num))
          (by intro h; have h2 := D.t2_order; rw [h, orderOf_one] at h2; exact absurd h2 (by norm_num))
          (by intro h; exact D.t2_nmem (by rw [← h]; exact D.t_mem))).1
      have hLle : L ≤ (D.S : Subgroup G) := by
        rw [hLdef, Subgroup.closure_le]
        rintro x (rfl | rfl)
        · exact D.S0_le D.t_mem
        · exact D.t2_mem
      have hrel : L.relIndex (D.S : Subgroup G) ≤ 2 := by
        have h := Subgroup.relIndex_mul_card L (D.S : Subgroup G)
        rw [inf_eq_left.mpr hLle, hcardL, hcardS8] at h
        omega
      refine ⟨c3deEF_conjAutU hDC g2, L, hτ2sq, hLle, hrel, hC, hτ2fix, ?_⟩
      · intro u hu l hl
        rw [hLdef] at hl
        have hu' : D.t2 * (u : G) * D.t2⁻¹ = (u : G) := by
          have h := congrArg (fun x : ↥C.P.U => (x : G)) hu
          rwa [c3deEF_conjAutU_apply_coe] at h
        have hcomm2 : D.t2 * (u : G) = (u : G) * D.t2 := by
          calc D.t2 * (u : G) = D.t2 * (u : G) * D.t2⁻¹ * D.t2 := by group
            _ = (u : G) * D.t2 := by rw [hu']
        have hcommt : D.t * (u : G) = (u : G) * D.t := by
          have h := C.t_comm_H (u : G) (C.P.H0_le_H (C.P.U_le_H0 u.2))
          rw [hDC.t_eq] at h
          exact h.symm
        exact c3deEF_closure_comm hcommt hcomm2 hl
    · -- ### Case B2: `σ = conj (t₁ t₂)`; `L = S₀`
      have hτ2swap : ∀ u, α₁ (c3deEF_conjAutU hDC g2 u)
          = α₂ (c3deEF_conjAutU hDC g12 u) := by
        intro u
        have h : c3deEF_conjAutU hDC g2 u
            = sigmaU C (c3deEF_conjAutU hDC g12 u) := by
          rw [hτ2rel]
          exact MulAut.mul_apply _ _ _ _
        rw [h]; exact hB _
      have hne2 : ¬ (∀ u, α₂ (c3deEF_conjAutU hDC g12 u) = α₁ u) := by
        intro h
        exact hC fun u => (hτ2swap u).trans (h u)
      have h2cases : (∀ u, α₂ (c3deEF_conjAutU hDC g12 u) = α₂ u)
          ∨ (∀ u, α₂ (c3deEF_conjAutU hDC g12 u) = α₁ u) := by
        rcases hsetτ with h | h
        · left
          intro u
          have hu := hsumτ u
          rw [h u] at hu
          exact add_left_cancel hu
        · right
          intro u
          have hu := hsumτ u
          rw [h u, add_comm (α₁ u) (α₂ u)] at hu
          exact add_left_cancel hu
      have h2τ : ∀ u, α₂ (c3deEF_conjAutU hDC g12 u) = α₂ u := by
        rcases h2cases with h | h
        · exact h
        · exact absurd h hne2
      have h1τ : ∀ u, α₁ (c3deEF_conjAutU hDC g12 u) = α₁ u := by
        intro u
        have hu := hsumτ u
        rw [h2τ u, add_comm (α₁ u) (α₂ u),
            add_comm (α₁ (c3deEF_conjAutU hDC g12 u)) (α₂ u)] at hu
        exact add_left_cancel hu
      refine ⟨c3deEF_conjAutU hDC g12, D.S0, hτtsq, D.S0_le,
        ?_, h1τ, h2τ, ?_⟩
      · exact le_of_eq D.S0_index
      · intro u hu l hl
        have hu' : (D.t1 * D.t2) * (u : G) * (D.t1 * D.t2)⁻¹ = (u : G) := by
          have h := congrArg (fun x : ↥C.P.U => (x : G)) hu
          rwa [c3deEF_conjAutU_apply_coe] at h
        have hcomm : (D.t1 * D.t2) * (u : G) = (u : G) * (D.t1 * D.t2) := by
          calc (D.t1 * D.t2) * (u : G)
              = (D.t1 * D.t2) * (u : G) * (D.t1 * D.t2)⁻¹ * (D.t1 * D.t2) := by group
            _ = (u : G) * (D.t1 * D.t2) := by rw [hu']
        have hlz : l ∈ Subgroup.zpowers (D.t1 * D.t2) := by rw [← D.gen]; exact hl
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hlz
        rw [← hk]
        exact (Commute.zpow_left hcomm k).eq

end Work.BG
