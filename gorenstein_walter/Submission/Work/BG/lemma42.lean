import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.deltaVanishB
import Submission.Work.BG.deltaAtTB
import Submission.Work.BG.s02_quot_data
import Submission.Work.BG.H0Conj
import Submission.Work.BG.kappaExists
import Submission.Work.BG.invJCard
import Submission.Work.BG.decompH1
import Submission.Work.BG.Hat
import Submission.Work.BG.HatUniq
import Submission.Work.BG.modTwoIndep
import Submission.Work.BG.thmCSmallAux
import Submission.Work.BG.CharBridge
import Submission.Work.BG.l42S4grid
import Submission.Work.BG.l42Ngrid
import Submission.Work.BG.l42BNinv
import Submission.Work.BG.l42HatOdd

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] [Fintype G]

/-! ## 0.  The subgroup `K = S · B` and its projection onto `B`

For Bender–Glauberman data `D` with `D.n = 2` the Sylow `2`-subgroup `S` is a Klein four
group, so `S` is abelian and `B ≤ C_G(S)` commutes with `S`; hence the product `S · B` is a
subgroup `K`, isomorphic to `S × B`.  The projection `K → B`, `σ b ↦ b`, is the map used to
describe the character `μ' = Ind_K^G(μ̂)` of Lemma 4.2. -/

/-- `K = S · B ≤ G`, for Bender–Glauberman data `D`. -/
noncomputable abbrev l42K (D : Work.GW2.BGData G) : Subgroup G :=
  (D.S : Subgroup G) ⊔ D.B

/-- `S` has order `4` when `D.n = 2` (`S ≅ DihedralGroup 2 ≅ V₄`). -/
theorem l42_S_card (D : Work.GW2.BGData G) (hn : D.n = 2) :
    Nat.card ↥(D.S : Subgroup G) = 4 := by
  obtain ⟨e⟩ := D.dih
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hn]

/-- `S ⊓ B = ⊥`. -/
theorem l42_S_inf_B (D : Work.GW2.BGData G) : (D.S : Subgroup G) ⊓ D.B = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  have hmem : x ∈ D.U ⊓ (D.S : Subgroup G) := ⟨hx.2.1.1, hx.1⟩
  rw [U_inf_S D] at hmem
  simpa using hmem

/-- `B` commutes elementwise with `S`. -/
theorem l42_comm (D : Work.GW2.BGData G) :
    ∀ σ ∈ (D.S : Subgroup G), ∀ b ∈ D.B, σ * b = b * σ :=
  fun σ hσ b hb => Subgroup.mem_centralizer_iff.mp (B_le_centralizer_S D hb) σ hσ

/-- An element of `K = S · B` is a product `σ · b`. -/
theorem l42_mem_K_iff (D : Work.GW2.BGData G) (x : G) :
    x ∈ l42K D ↔ ∃ σ ∈ (D.S : Subgroup G), ∃ b ∈ D.B, x = σ * b := by
  have hBN : D.B ≤ Subgroup.normalizer ((D.S : Subgroup G) : Set G) :=
    (B_le_centralizer_S D).trans (Subgroup.centralizer_le_normalizer _)
  rw [← SetLike.mem_coe,
    Subgroup.coe_mul_of_right_le_normalizer_left (D.S : Subgroup G) D.B hBN,
    Set.mem_mul]
  constructor
  · rintro ⟨σ, hσ, b, hb, hσb⟩
    exact ⟨σ, hσ, b, hb, hσb.symm⟩
  · rintro ⟨σ, hσ, b, hb, rfl⟩
    exact ⟨σ, hσ, b, hb, rfl⟩

/-- Unique factorisation of an element of `K = S · B` as `σ · b`. -/
theorem l42_existsUnique (D : Work.GW2.BGData G) (h : ↥(l42K D)) :
    ∃! p : ↥(D.S : Subgroup G) × ↥D.B, (p.1 : G) * (p.2 : G) = (h : G) := by
  obtain ⟨σ, hσ, b, hb, hσb⟩ := (l42_mem_K_iff D (h : G)).mp h.2
  refine ⟨(⟨σ, hσ⟩, ⟨b, hb⟩), hσb.symm, ?_⟩
  intro y hy
  exact mul_injective_of_inf_eq_bot (A := (D.S : Subgroup G)) (B := D.B) (l42_S_inf_B D)
    (by simpa using hy.trans hσb)

/-- The `S`-component of an element of `K`. -/
noncomputable def l42sOf (D : Work.GW2.BGData G) (h : ↥(l42K D)) : ↥(D.S : Subgroup G) :=
  (Classical.choose (l42_existsUnique D h)).1

/-- The `B`-component of an element of `K`. -/
noncomputable def l42bOf (D : Work.GW2.BGData G) (h : ↥(l42K D)) : ↥D.B :=
  (Classical.choose (l42_existsUnique D h)).2

theorem l42_sOf_mul_bOf (D : Work.GW2.BGData G) (h : ↥(l42K D)) :
    (l42sOf D h : G) * (l42bOf D h : G) = (h : G) :=
  (Classical.choose_spec (l42_existsUnique D h)).1

theorem l42_eq_of_mul (D : Work.GW2.BGData G) {σ : G} (hσ : σ ∈ (D.S : Subgroup G))
    {b : G} (hb : b ∈ D.B) (h : ↥(l42K D)) (hh : (h : G) = σ * b) :
    ((l42sOf D h : G) = σ) ∧ ((l42bOf D h : G) = b) := by
  have hspec := (Classical.choose_spec (l42_existsUnique D h)).2 (⟨σ, hσ⟩, ⟨b, hb⟩)
    (by simpa using hh.symm)
  refine ⟨?_, ?_⟩
  · exact (congrArg (fun p : ↥(D.S : Subgroup G) × ↥D.B => (p.1 : G)) hspec).symm
  · exact (congrArg (fun p : ↥(D.S : Subgroup G) × ↥D.B => (p.2 : G)) hspec).symm

/-- The projection `K → B`, well-defined by uniqueness of the factorisation. -/
noncomputable def l42projB (D : Work.GW2.BGData G) : ↥(l42K D) →* ↥D.B where
  toFun := fun h => l42bOf D h
  map_one' := by
    have hh : ((1 : ↥(l42K D)) : G) = ((1 : ↥(D.S : Subgroup G)) : G) * ((1 : ↥D.B) : G) := by
      simp
    have h2 := (l42_eq_of_mul D (D.S : Subgroup G).one_mem D.B.one_mem (1 : ↥(l42K D)) hh).2
    exact Subtype.ext h2
  map_mul' := by
    intro x y
    have hxs : (l42sOf D x : G) ∈ (D.S : Subgroup G) := (l42sOf D x).2
    have hxb : (l42bOf D x : G) ∈ D.B := (l42bOf D x).2
    have hys : (l42sOf D y : G) ∈ (D.S : Subgroup G) := (l42sOf D y).2
    have hyb : (l42bOf D y : G) ∈ D.B := (l42bOf D y).2
    apply Subtype.ext
    have hh : ((x * y : ↥(l42K D)) : G) =
        ((l42sOf D x * l42sOf D y : ↥(D.S : Subgroup G)) : G) *
          ((l42bOf D x * l42bOf D y : ↥D.B) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
        ← l42_sOf_mul_bOf D x, ← l42_sOf_mul_bOf D y]
      calc ((l42sOf D x : G) * (l42bOf D x : G)) *
              ((l42sOf D y : G) * (l42bOf D y : G))
          = (l42sOf D x : G) * ((l42bOf D x : G) * (l42sOf D y : G)) * (l42bOf D y : G) := by
            group
        _ = (l42sOf D x : G) * ((l42sOf D y : G) * (l42bOf D x : G)) * (l42bOf D y : G) := by
            rw [l42_comm D (l42sOf D y) hys (l42bOf D x) hxb]
        _ = ((l42sOf D x : G) * (l42sOf D y : G)) *
              ((l42bOf D x : G) * (l42bOf D y : G)) := by group
    have h2 := (l42_eq_of_mul D ((D.S : Subgroup G).mul_mem hxs hys) (D.B.mul_mem hxb hyb)
      (x * y) hh).2
    exact h2

/-- `l42projB` sends `σ · b` to `b`. -/
theorem l42projB_mul (D : Work.GW2.BGData G) {σ : G} (hσ : σ ∈ (D.S : Subgroup G))
    {b : G} (hb : b ∈ D.B) :
    ((l42projB D ⟨σ * b, Subgroup.mul_mem_sup hσ hb⟩ : ↥D.B) : G) = b :=
  (l42_eq_of_mul D hσ hb ⟨σ * b, Subgroup.mul_mem_sup hσ hb⟩ rfl).2

/-! ## 1.  Pullback of a character along a monoid homomorphism -/

/-- The pullback of a genuine character along a monoid homomorphism is a genuine character
(it is the character of the composed representation). -/
theorem l42_isCharacter_pullback {H G : Type*} [Group H] [Group G] {f : H →* G}
    {φ : ClassFunction G ℂ} (hφ : IsCharacter φ) : IsCharacter (ClassFunction.compHom f φ) := by
  obtain ⟨V, _, _, _, ρ, hρ⟩ := hφ
  refine ⟨V, inferInstance, inferInstance, inferInstance, ρ.comp f, ?_⟩
  ext h
  rw [ClassFunction.compHom_apply]
  exact congrFun hρ (f h)

variable (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)

/-! ## 2.  The conjugation action of `N_G(S)` on class functions of `B` -/

/-- The automorphism `b ↦ x b x⁻¹` of `B`, for `x` normalising `B` on both sides. -/
noncomputable abbrev l42conjAutB (x : G)
    (hx : ∀ b ∈ D.B, x * b * x⁻¹ ∈ D.B) (hx' : ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B) :
    ↥D.B ≃* ↥D.B where
  toFun b := ⟨x * (b : G) * x⁻¹, hx b b.2⟩
  invFun b := ⟨x⁻¹ * (b : G) * x, hx' b b.2⟩
  left_inv b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  right_inv b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  map_mul' b c := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

/-- `θ^x`, the conjugate of a class function of `B` by `x ∈ N_G(S)`. -/
noncomputable abbrev l42conjCF (x : G)
    (hx : ∀ b ∈ D.B, x * b * x⁻¹ ∈ D.B) (hx' : ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B)
    (θ : ClassFunction ↥D.B ℂ) : ClassFunction ↥D.B ℂ :=
  ClassFunction.compHom (l42conjAutB D x hx hx').toMonoidHom θ

theorem l42conjCF_apply (x : G)
    (hx : ∀ b ∈ D.B, x * b * x⁻¹ ∈ D.B) (hx' : ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B)
    (θ : ClassFunction ↥D.B ℂ) (b : ↥D.B) :
    l42conjCF D x hx hx' θ b = θ ⟨x * (b : G) * x⁻¹, hx b b.2⟩ :=
  ClassFunction.compHom_apply _ θ b

/-! ## 3.  `ν|_B` and the construction of `μ'` -/

/-- `B ↪ H₀` (`B ≤ U ≤ H₀`). -/
noncomputable def l42incl (hc : Compat D C) : ↥D.B →* ↥C.P.H0 where
  toFun b := ⟨(b : G), C.P.U_le_H0 (by rw [hc.U_eq]; exact mem_DU_of_mem_B D b.2)⟩
  map_one' := Subtype.ext rfl
  map_mul' a b := Subtype.ext rfl

@[simp] theorem l42incl_coe (hc : Compat D C) (b : ↥D.B) :
    ((l42incl D C hc b : ↥C.P.H0) : G) = (b : G) := rfl

/-- `ν|_B`, the restriction of a class function of `H₀` to `B`. -/
noncomputable def l42nuB (hc : Compat D C) (ν : ClassFunction ↥C.P.H0 ℂ) :
    ClassFunction ↥D.B ℂ :=
  ClassFunction.compHom (l42incl D C hc) ν

@[simp] theorem l42nuB_apply (hc : Compat D C) (ν : ClassFunction ↥C.P.H0 ℂ) (b : ↥D.B) :
    l42nuB D C hc ν b = ν (l42incl D C hc b) :=
  ClassFunction.compHom_apply _ ν b

/-- `ν|_B` is a virtual character of `B`. -/
theorem l42nuB_mem_ZIrr (hc : Compat D C) (ν : ClassFunction ↥C.P.H0 ℂ)
    (hν : IsIrreducibleCharacter ν) : l42nuB D C hc ν ∈ ZIrr ↥D.B :=
  IsCharacter.mem_ZIrr (l42_isCharacter_pullback hν.isCharacter)

/-- `μ̂` extended trivially across `S` to `K = S · B`, then induced to `G`. -/
noncomputable abbrev l42muPrime [Fintype ↥(l42K D)] [Invertible (Nat.card ↥(l42K D) : ℂ)]
    (θ : ClassFunction ↥D.B ℂ) : ClassFunction G ℂ :=
  ClassFunction.induce (l42K D) (ClassFunction.compHom (l42projB D) θ)

theorem l42muPrime_mem_ZIrr [Fintype ↥(l42K D)] [Invertible (Nat.card ↥(l42K D) : ℂ)]
    (θ : ClassFunction ↥D.B ℂ) (hθ : IsIrreducibleCharacter θ) :
    l42muPrime D θ ∈ ZIrr G :=
  ClassFunction.induce_mem_ZIrr (l42K D) (θ := ClassFunction.compHom (l42projB D) θ)
    (l42_isCharacter_pullback hθ.isCharacter).mem_ZIrr

/-! ## 4.  The bijection `S × B ≃ K` and `|K| = 4|B|` -/

/-- `↥S × ↥B ≃ ↥(S · B)`, `(σ, b) ↦ σ b`. -/
noncomputable def l42eK : ↥(D.S : Subgroup G) × ↥D.B ≃ ↥(l42K D) where
  toFun p := ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  invFun h := (l42sOf D h, l42bOf D h)
  left_inv p := by
    obtain ⟨⟨σ, hσ⟩, ⟨b, hb⟩⟩ := p
    refine Prod.ext ?_ ?_
    · exact Subtype.ext (l42_eq_of_mul D hσ hb ⟨σ * b, Subgroup.mul_mem_sup hσ hb⟩ rfl).1
    · exact Subtype.ext (l42_eq_of_mul D hσ hb ⟨σ * b, Subgroup.mul_mem_sup hσ hb⟩ rfl).2
  right_inv h := Subtype.ext (l42_sOf_mul_bOf D h)

@[simp] theorem l42eK_coe (p : ↥(D.S : Subgroup G) × ↥D.B) :
    ((l42eK D p : ↥(l42K D)) : G) = (p.1 : G) * (p.2 : G) := rfl

theorem l42card_K (hn : D.n = 2) : Nat.card ↥(l42K D) = 4 * Nat.card ↥D.B := by
  rw [← Nat.card_congr (l42eK D), Nat.card_prod, l42_S_card D hn]

/-! ## 5.  Frobenius reciprocity and reindexing -/

theorem l42_inner_eq (hc : Compat D C) (β₂ : quotGroup C.P →* ℂˣ)
    (ν : ClassFunction ↥C.P.H0 ℂ) (θ : ClassFunction ↥D.B ℂ)
    [Fintype ↥(D.S : Subgroup G)] [Fintype ↥D.B]
    [Fintype ↥(l42K D)] [Invertible (Nat.card ↥(l42K D) : ℂ)]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    ClassFunction.inner (delta C β₂ ν) (l42muPrime D θ) =
      ⅟((Nat.card ↥(l42K D) : ℂ)) *
        ∑ σ : ↥(D.S : Subgroup G), ∑ b : ↥D.B,
          delta C β₂ ν ((σ : G) * (b : G)) * star (θ b) := by
  have hF : ClassFunction.inner (delta C β₂ ν) (l42muPrime D θ) =
      ClassFunction.inner (ClassFunction.restrict (l42K D) (delta C β₂ ν))
        (ClassFunction.compHom (l42projB D) θ) := by
    have h := ClassFunction.inner_induce_eq_inner_restrict (l42K D)
      (ClassFunction.compHom (l42projB D) θ) (delta C β₂ ν)
    calc ClassFunction.inner (delta C β₂ ν) (l42muPrime D θ)
        = star (ClassFunction.inner (l42muPrime D θ) (delta C β₂ ν)) :=
            OddOrder.RepresentationTheory.inner_conj_symm _ _
      _ = star (ClassFunction.inner (ClassFunction.compHom (l42projB D) θ)
            (ClassFunction.restrict (l42K D) (delta C β₂ ν))) := by rw [h]
      _ = ClassFunction.inner (ClassFunction.restrict (l42K D) (delta C β₂ ν))
            (ClassFunction.compHom (l42projB D) θ) :=
            (OddOrder.RepresentationTheory.inner_conj_symm _ _).symm
  rw [hF, ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum]
  congr 1
  rw [← Equiv.sum_comp (l42eK D)
    (fun h : ↥(l42K D) =>
      (ClassFunction.restrict (l42K D) (delta C β₂ ν)) h *
        star ((ClassFunction.compHom (l42projB D) θ) h))]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun b _ => ?_
  have hproj : l42projB D (l42eK D (σ, b)) = b := Subtype.ext (l42projB_mul D σ.2 b.2)
  simp only [ClassFunction.restrict_apply, l42eK_coe, ClassFunction.compHom_apply, hproj]

/-! ## 6.  Conjugation by normalizer elements, uniformly -/

/-- `N_G(S)` normalises `B` (first half of Bender–Glauberman's `NOrbBInv`). -/
def l42NBinv (D : Work.GW2.BGData G) : Prop :=
  ∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G), ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B

theorem l42BNinv_swap (h : l42NBinv D) {x : G}
    (hx : x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G)) :
    ∀ b ∈ D.B, x * b * x⁻¹ ∈ D.B := by
  intro b hb
  have h' := h x⁻¹ ((Subgroup.normalizer ((D.S : Subgroup G) : Set G)).inv_mem hx) b hb
  simpa using h'

/-- The automorphism `b ↦ x b x⁻¹` of `B` for `x ∈ N_G(S)`. -/
noncomputable abbrev l42conjAutN (h : l42NBinv D) (x : G)
    (hx : x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G)) : ↥D.B ≃* ↥D.B :=
  l42conjAutB D x (l42BNinv_swap D h hx) (h x hx)

/-- `θ^x` for `x ∈ N_G(S)`. -/
noncomputable abbrev l42conjNCF (h : l42NBinv D) (x : G)
    (hx : x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G))
    (θ : ClassFunction ↥D.B ℂ) : ClassFunction ↥D.B ℂ :=
  ClassFunction.compHom (l42conjAutN D h x hx).toMonoidHom θ

@[simp] theorem l42conjAutN_apply (h : l42NBinv D) {x : G}
    (hx : x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G)) (b : ↥D.B) :
    l42conjAutN D h x hx b = ⟨x * (b : G) * x⁻¹, l42BNinv_swap D h hx b b.2⟩ := rfl

@[simp] theorem l42conjAutN_toMonoidHom_apply (h : l42NBinv D) {x : G}
    (hx : x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G)) (b : ↥D.B) :
    (l42conjAutN D h x hx).toMonoidHom b
      = ⟨x * (b : G) * x⁻¹, l42BNinv_swap D h hx b b.2⟩ := rfl

@[simp] theorem l42conjNCF_apply (h : l42NBinv D) (x : G)
    (hx : x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G))
    (θ : ClassFunction ↥D.B ℂ) (b : ↥D.B) :
    l42conjNCF D h x hx θ b = θ ⟨x * (b : G) * x⁻¹, l42BNinv_swap D h hx b b.2⟩ := rfl

theorem l42conjNCF_cancel (h : l42NBinv D) (x : G)
    (hx : x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G))
    (θ : ClassFunction ↥D.B ℂ) :
    l42conjNCF D h x⁻¹ ((Subgroup.normalizer ((D.S : Subgroup G) : Set G)).inv_mem hx)
        (l42conjNCF D h x hx θ) = θ := by
  ext b
  rw [l42conjNCF_apply, l42conjNCF_apply]
  refine congrArg θ (Subtype.ext ?_)
  group

/-- Elements of `C_G(S)` act trivially on class functions of `B`: conjugation by them is an
inner automorphism of `B` (second half of `NOrbBInv`). -/
theorem l42conjNCF_centralizer (h : l42NBinv D)
    (hC : ∀ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), ∀ b ∈ D.B,
        ∃ b₀ ∈ D.B, c⁻¹ * b * c = b₀ * b * b₀⁻¹)
    {c : G} (hc : c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G))
    (θ : ClassFunction ↥D.B ℂ) :
    l42conjNCF D h c (Subgroup.centralizer_le_normalizer _ hc) θ = θ := by
  ext b
  rw [l42conjNCF_apply]
  obtain ⟨b₀, hb₀, hconj⟩ := hC c⁻¹
    ((Subgroup.centralizer ((D.S : Subgroup G) : Set G)).inv_mem hc) b b.2
  have hE : (⟨c * (b : G) * c⁻¹,
        l42BNinv_swap D h (Subgroup.centralizer_le_normalizer _ hc) b b.2⟩ : ↥D.B)
      = (⟨b₀, hb₀⟩ : ↥D.B) * b * (⟨b₀, hb₀⟩ : ↥D.B)⁻¹ := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using hconj
  rw [hE]
  exact θ.conj_eq b ⟨b₀, hb₀⟩

/-! ## 7.  The value of `δ_ν` on `S · b` -/

theorem l42_sum_S [Fintype ↥(D.S : Subgroup G)] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hc : Compat D C) (hn : D.n = 2)
    (β₂ : quotGroup C.P →* ℂˣ) (hβ : β₂ ≠ 1)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ S4Index C)
    (hSelm : ∀ σ : ↥(D.S : Subgroup G), σ = 1 ∨ (σ : G) = D.t ∨ (σ : G) = D.t1 ∨ (σ : G) = D.t2)
    (ht_ne_t1 : (D.t : G) ≠ D.t1) (ht_ne_t2 : (D.t : G) ≠ D.t2) (ht1_ne_t2 : D.t1 ≠ D.t2)
    {n : G} (hnt : n * D.t * n⁻¹ = D.t1) (hnt2 : n ^ 2 * D.t * (n ^ 2)⁻¹ = D.t2)
    (hBt : ∀ b ∈ D.B, n⁻¹ * b * (n⁻¹)⁻¹ ∈ D.B)
    (hBt2 : ∀ b ∈ D.B, (n ^ 2)⁻¹ * b * ((n ^ 2)⁻¹)⁻¹ ∈ D.B)
    (b : ↥D.B) :
    (∑ σ : ↥(D.S : Subgroup G), delta C β₂ ν ((σ : G) * (b : G))) =
      4 * (l42nuB D C hc ν b
        + l42nuB D C hc ν ⟨n⁻¹ * (b : G) * (n⁻¹)⁻¹, hBt b b.2⟩
        + l42nuB D C hc ν ⟨(n ^ 2)⁻¹ * (b : G) * ((n ^ 2)⁻¹)⁻¹, hBt2 b b.2⟩) := by
  classical
  have ht_ne_one : (D.t : G) ≠ 1 := ((orderOf_eq_prime_iff (p := 2)).mp D.t_order).2
  have ht1_ne_one : (D.t1 : G) ≠ 1 := ((orderOf_eq_prime_iff (p := 2)).mp D.t1_order).2
  have ht2_ne_one : (D.t2 : G) ≠ 1 := ((orderOf_eq_prime_iff (p := 2)).mp D.t2_order).2
  have hUniv : (Finset.univ : Finset ↥(D.S : Subgroup G)) =
      ({⟨1, (D.S : Subgroup G).one_mem⟩, ⟨D.t, D.S0_le D.t_mem⟩, ⟨D.t1, D.t1_mem⟩,
        ⟨D.t2, D.t2_mem⟩} : Finset ↥(D.S : Subgroup G)) := by
    symm
    apply Finset.eq_univ_iff_forall.mpr
    intro σ
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hSelm σ with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
  have h1 : (⟨1, (D.S : Subgroup G).one_mem⟩ : ↥(D.S : Subgroup G)) ∉
      ({⟨D.t, D.S0_le D.t_mem⟩, ⟨D.t1, D.t1_mem⟩, ⟨D.t2, D.t2_mem⟩} :
        Finset ↥(D.S : Subgroup G)) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact ht_ne_one ((congrArg Subtype.val h).symm)
    · exact ht1_ne_one ((congrArg Subtype.val h).symm)
    · exact ht2_ne_one ((congrArg Subtype.val h).symm)
  have h2 : (⟨D.t, D.S0_le D.t_mem⟩ : ↥(D.S : Subgroup G)) ∉
      ({⟨D.t1, D.t1_mem⟩, ⟨D.t2, D.t2_mem⟩} : Finset ↥(D.S : Subgroup G)) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact ht_ne_t1 (congrArg Subtype.val h)
    · exact ht_ne_t2 (congrArg Subtype.val h)
  have h3 : (⟨D.t1, D.t1_mem⟩ : ↥(D.S : Subgroup G)) ∉
      ({⟨D.t2, D.t2_mem⟩} : Finset ↥(D.S : Subgroup G)) := by
    rw [Finset.mem_singleton]
    exact fun h => ht1_ne_t2 (congrArg Subtype.val h)
  have h0 : delta C β₂ ν (((⟨1, (D.S : Subgroup G).one_mem⟩ : ↥(D.S : Subgroup G)) : G)
        * (b : G)) = 0 := by
    change delta C β₂ ν ((1 : G) * (b : G)) = 0
    rw [one_mul]
    exact deltaVanishB D C hc hn β₂ hβ ν hν (b : G) b.2
  have hT : delta C β₂ ν (((⟨D.t, D.S0_le D.t_mem⟩ : ↥(D.S : Subgroup G)) : G) * (b : G))
      = 4 * l42nuB D C hc ν b := by
    change delta C β₂ ν (D.t * (b : G)) = 4 * l42nuB D C hc ν b
    have h := deltaAtTB D C hc hn β₂ hβ ν hν (l42incl D C hc b) b.2
    simpa only [l42incl_coe, hc.t_eq, l42nuB_apply] using h
  have hT1 : delta C β₂ ν (((⟨D.t1, D.t1_mem⟩ : ↥(D.S : Subgroup G)) : G) * (b : G))
      = 4 * l42nuB D C hc ν ⟨n⁻¹ * (b : G) * (n⁻¹)⁻¹, hBt b b.2⟩ := by
    change delta C β₂ ν (D.t1 * (b : G)) =
      4 * l42nuB D C hc ν ⟨n⁻¹ * (b : G) * (n⁻¹)⁻¹, hBt b b.2⟩
    rw [← hnt]
    have hg : n * D.t * n⁻¹ * (b : G)
        = n * (D.t * (n⁻¹ * (b : G) * (n⁻¹)⁻¹)) * n⁻¹ := by group
    rw [hg, (delta C β₂ ν).conj_eq (D.t * (n⁻¹ * (b : G) * (n⁻¹)⁻¹)) n]
    have h := deltaAtTB D C hc hn β₂ hβ ν hν
      (l42incl D C hc ⟨n⁻¹ * (b : G) * (n⁻¹)⁻¹, hBt b b.2⟩) (hBt b b.2)
    simpa only [l42incl_coe, hc.t_eq, l42nuB_apply] using h
  have hT2 : delta C β₂ ν (((⟨D.t2, D.t2_mem⟩ : ↥(D.S : Subgroup G)) : G) * (b : G))
      = 4 * l42nuB D C hc ν ⟨(n ^ 2)⁻¹ * (b : G) * ((n ^ 2)⁻¹)⁻¹, hBt2 b b.2⟩ := by
    change delta C β₂ ν (D.t2 * (b : G)) =
      4 * l42nuB D C hc ν ⟨(n ^ 2)⁻¹ * (b : G) * ((n ^ 2)⁻¹)⁻¹, hBt2 b b.2⟩
    rw [← hnt2]
    have hg : n ^ 2 * D.t * (n ^ 2)⁻¹ * (b : G)
        = n ^ 2 * (D.t * ((n ^ 2)⁻¹ * (b : G) * ((n ^ 2)⁻¹)⁻¹)) * (n ^ 2)⁻¹ := by group
    rw [hg, (delta C β₂ ν).conj_eq (D.t * ((n ^ 2)⁻¹ * (b : G) * ((n ^ 2)⁻¹)⁻¹)) (n ^ 2)]
    have h := deltaAtTB D C hc hn β₂ hβ ν hν
      (l42incl D C hc ⟨(n ^ 2)⁻¹ * (b : G) * ((n ^ 2)⁻¹)⁻¹, hBt2 b b.2⟩) (hBt2 b b.2)
    simpa only [l42incl_coe, hc.t_eq, l42nuB_apply] using h
  rw [hUniv, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
    Finset.sum_singleton, h0, hT, hT1, hT2]
  ring

/-! ## 8.  `(δ_ν, μ')` as a sum of three inner products on `B` -/

theorem l42_inner_sum [Fintype ↥(D.S : Subgroup G)] [Fintype ↥D.B] [Fintype ↥(l42K D)]
    [Invertible (Nat.card ↥(l42K D) : ℂ)] [Invertible (Nat.card ↥D.B : ℂ)]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hc : Compat D C) (hn : D.n = 2)
    (β₂ : quotGroup C.P →* ℂˣ) (hβ : β₂ ≠ 1)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ S4Index C)
    (hSelm : ∀ σ : ↥(D.S : Subgroup G), σ = 1 ∨ (σ : G) = D.t ∨ (σ : G) = D.t1 ∨ (σ : G) = D.t2)
    (ht_ne_t1 : (D.t : G) ≠ D.t1) (ht_ne_t2 : (D.t : G) ≠ D.t2) (ht1_ne_t2 : D.t1 ≠ D.t2)
    {n : G} (hnt : n * D.t * n⁻¹ = D.t1) (hnt2 : n ^ 2 * D.t * (n ^ 2)⁻¹ = D.t2)
    (hBt : ∀ b ∈ D.B, n⁻¹ * b * (n⁻¹)⁻¹ ∈ D.B)
    (hBt2 : ∀ b ∈ D.B, (n ^ 2)⁻¹ * b * ((n ^ 2)⁻¹)⁻¹ ∈ D.B)
    (hBtin : ∀ b ∈ D.B, (n⁻¹)⁻¹ * b * n⁻¹ ∈ D.B)
    (hBt2in : ∀ b ∈ D.B, ((n ^ 2)⁻¹)⁻¹ * b * (n ^ 2)⁻¹ ∈ D.B)
    (θ : ClassFunction ↥D.B ℂ) :
    ClassFunction.inner (delta C β₂ ν) (l42muPrime D θ) =
      ClassFunction.inner (l42nuB D C hc ν) θ
        + ClassFunction.inner (l42conjCF D n⁻¹ hBt hBtin (l42nuB D C hc ν)) θ
        + ClassFunction.inner (l42conjCF D (n ^ 2)⁻¹ hBt2 hBt2in (l42nuB D C hc ν)) θ := by
  classical
  set A0 : ClassFunction ↥D.B ℂ := l42nuB D C hc ν with hA0
  set A1 : ClassFunction ↥D.B ℂ := l42conjCF D n⁻¹ hBt hBtin (l42nuB D C hc ν) with hA1
  set A2 : ClassFunction ↥D.B ℂ := l42conjCF D (n ^ 2)⁻¹ hBt2 hBt2in (l42nuB D C hc ν) with hA2
  have hsum : (∑ σ : ↥(D.S : Subgroup G), ∑ b : ↥D.B,
        delta C β₂ ν ((σ : G) * (b : G)) * star (θ b))
      = 4 * ∑ b : ↥D.B, (A0 b + A1 b + A2 b) * star (θ b) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hA1b : l42conjCF D n⁻¹ hBt hBtin (l42nuB D C hc ν) b
        = l42nuB D C hc ν ⟨n⁻¹ * (b : G) * (n⁻¹)⁻¹, hBt b b.2⟩ := rfl
    have hA2b : l42conjCF D (n ^ 2)⁻¹ hBt2 hBt2in (l42nuB D C hc ν) b
        = l42nuB D C hc ν ⟨(n ^ 2)⁻¹ * (b : G) * ((n ^ 2)⁻¹)⁻¹, hBt2 b b.2⟩ := rfl
    rw [← Finset.sum_mul,
      l42_sum_S D C hc hn β₂ hβ hν hSelm ht_ne_t1 ht_ne_t2 ht1_ne_t2 hnt hnt2 hBt hBt2 b,
      ← hA1b, ← hA2b, ← hA1, ← hA2, ← hA0]
    ring
  have hK : ((Nat.card ↥(l42K D) : ℕ) : ℂ) = 4 * (Nat.card ↥D.B : ℂ) := by
    rw [l42card_K D hn]; push_cast; ring
  rw [l42_inner_eq D C hc β₂ ν θ, hsum, invOf_eq_inv, hK,
    ClassFunction.inner_eq_inv_card_mul_innerSum,
    ClassFunction.inner_eq_inv_card_mul_innerSum,
    ClassFunction.inner_eq_inv_card_mul_innerSum]
  simp only [ClassFunction.innerSum, invOf_eq_inv]
  have hpt : ∀ b : ↥D.B, (A0 b + A1 b + A2 b) * star (θ b)
      = A0 b * star (θ b) + A1 b * star (θ b) + A2 b * star (θ b) := fun b => by ring
  rw [Finset.sum_congr rfl (fun b _ => hpt b), Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  have hB : (Nat.card ↥D.B : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp

/-! ## 9.  The conjugation action of `N_G(S)` on `Irr(B)`, and its counting properties -/

theorem l42conjNCF_zero (h : l42NBinv D) (θ : ClassFunction ↥D.B ℂ) :
    l42conjNCF D h 1 (Subgroup.one_mem _) θ = θ := by
  ext b
  rw [l42conjNCF_apply]
  refine congrArg θ (Subtype.ext ?_)
  group

theorem l42conjNCF_mul (h : l42NBinv D) {x y : G}
    (hx : x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G))
    (hy : y ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G))
    (θ : ClassFunction ↥D.B ℂ) :
    l42conjNCF D h x hx (l42conjNCF D h y hy θ) = l42conjNCF D h (y * x)
      (Subgroup.mul_mem _ hy hx) θ := by
  ext b
  rw [l42conjNCF_apply, l42conjNCF_apply, l42conjNCF_apply]
  refine congrArg θ (Subtype.ext ?_)
  group

/-- Elements of `C_G(S)` do not change the `N_G(S)`-conjugates of a class function of `B`. -/
theorem l42conjNCF_centralizer_mul (h : l42NBinv D)
    (hC : ∀ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), ∀ b ∈ D.B,
        ∃ b₀ ∈ D.B, c⁻¹ * b * c = b₀ * b * b₀⁻¹)
    {c x : G} (hc : c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G))
    (hx : x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G))
    (θ : ClassFunction ↥D.B ℂ) :
    l42conjNCF D h (c * x)
        (Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer _ hc) hx) θ
      = l42conjNCF D h x hx θ := by
  ext b
  rw [l42conjNCF_apply, l42conjNCF_apply]
  have hzx : x * (b : G) * x⁻¹ ∈ D.B := l42BNinv_swap D h hx b b.2
  obtain ⟨b₀, hb₀, hconj⟩ := hC c⁻¹
    ((Subgroup.centralizer ((D.S : Subgroup G) : Set G)).inv_mem hc)
    (x * (b : G) * x⁻¹) hzx
  have hB : (⟨(c * x) * (b : G) * (c * x)⁻¹,
        l42BNinv_swap D h (Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer _ hc) hx) b b.2⟩
      : ↥D.B) = (⟨b₀, hb₀⟩ : ↥D.B) * ⟨x * (b : G) * x⁻¹, hzx⟩ * (⟨b₀, hb₀⟩ : ↥D.B)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    rw [← hconj]
    group
  rw [hB]
  exact θ.conj_eq ⟨x * (b : G) * x⁻¹, hzx⟩ ⟨b₀, hb₀⟩

theorem l42conjNCF_inner (h : l42NBinv D) {y : G}
    (hy : y ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G))
    [Fintype ↥D.B] [Invertible (Nat.card ↥D.B : ℂ)]
    (φ θ : ClassFunction ↥D.B ℂ) :
    ClassFunction.inner (l42conjNCF D h y⁻¹
        ((Subgroup.normalizer ((D.S : Subgroup G) : Set G)).inv_mem hy) φ) θ =
      ClassFunction.inner φ (l42conjNCF D h y hy θ) := by
  have hcomp : ClassFunction.compHom
      (l42conjAutN D h y⁻¹ ((Subgroup.normalizer ((D.S : Subgroup G) : Set G)).inv_mem hy)).toMonoidHom
      (ClassFunction.compHom (l42conjAutN D h y hy).toMonoidHom θ) = θ := by
    ext b
    rw [ClassFunction.compHom_apply, ClassFunction.compHom_apply]
    refine congrArg θ (Subtype.ext ?_)
    simp only [l42conjAutN_toMonoidHom_apply]
    group
  have h2 := ClassFunction.inner_compHom_mulEquiv
    (l42conjAutN D h y⁻¹ ((Subgroup.normalizer ((D.S : Subgroup G) : Set G)).inv_mem hy))
    φ (ClassFunction.compHom (l42conjAutN D h y hy).toMonoidHom θ)
  rw [hcomp] at h2
  exact h2

theorem l42conjNCF_irreducible (h : l42NBinv D) {x : G}
    (hx : x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G))
    {θ : ClassFunction ↥D.B ℂ} (hθ : IsIrreducibleCharacter θ) :
    IsIrreducibleCharacter (l42conjNCF D h x hx θ) := by
  rw [l42conjNCF]
  exact IsIrreducibleCharacter.compHom_of_surjective (l42conjAutN D h x hx).surjective hθ

/-- `n³ ∈ C_G(S)`: otherwise `n² ∈ C_G(S)` would contradict `n² t n⁻² = t₂`, or `n ∈ C_G(S)`
would contradict `n t n⁻¹ = t₁`. -/
theorem l42pow3_mem {n : G} (hnN : n ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G))
    (hnt : n * D.t * n⁻¹ = D.t1) (hnt2 : n ^ 2 * D.t * (n ^ 2)⁻¹ = D.t2)
    (ht_ne_t1 : (D.t : G) ≠ D.t1) (ht_ne_t2 : (D.t : G) ≠ D.t2)
    (hcover : ∀ y ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
        y ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) ∨
        (∃ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), y = c * n) ∨
        (∃ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), y = c * n ^ 2)) :
    n ^ 3 ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) := by
  have h3N : n ^ 3 ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G) := by
    have h2 : n ^ 2 ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G) := by
      simpa only [pow_two] using Subgroup.mul_mem _ hnN hnN
    have h := Subgroup.mul_mem _ h2 hnN
    simpa only [pow_succ] using h
  rcases hcover (n ^ 3) h3N with h | ⟨c, hc, h⟩ | ⟨c, hc, h⟩
  · exact h
  · exfalso
    have hn2 : n ^ 2 = c := by
      have h' : n ^ 3 * n⁻¹ = c * n * n⁻¹ := by rw [h]
      simpa [pow_succ, mul_assoc] using h'
    have hmem : n ^ 2 ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) := hn2 ▸ hc
    have hcomm : D.t * n ^ 2 = n ^ 2 * D.t :=
      Subgroup.mem_centralizer_iff.mp hmem D.t (D.S0_le D.t_mem)
    have : n ^ 2 * D.t * (n ^ 2)⁻¹ = D.t := by
      rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [this] at hnt2
    exact ht_ne_t2 hnt2
  · exfalso
    have hn : n = c := by
      have h' : n ^ 3 * (n ^ 2)⁻¹ = c * n ^ 2 * (n ^ 2)⁻¹ := by rw [h]
      simpa [pow_succ, mul_assoc] using h'
    have hmem : n ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) := hn ▸ hc
    have hcomm : D.t * n = n * D.t :=
      Subgroup.mem_centralizer_iff.mp hmem D.t (D.S0_le D.t_mem)
    have : n * D.t * n⁻¹ = D.t := by
      rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [this] at hnt
    exact ht_ne_t1 hnt

theorem l42conjNCF_congr (hBN : l42NBinv D) (θ : ClassFunction ↥D.B ℂ) {a b : G}
    (ha : a ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G))
    (hb : b ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G)) (hab : a = b) :
    l42conjNCF D hBN a ha θ = l42conjNCF D hBN b hb θ :=
  congrArg (fun p : ↥(Subgroup.normalizer ((D.S : Subgroup G) : Set G)) =>
    l42conjNCF D hBN p.1 p.2 θ)
    (show (⟨a, ha⟩ : ↥(Subgroup.normalizer ((D.S : Subgroup G) : Set G))) = ⟨b, hb⟩
      from Subtype.ext hab)

/-! ## 10.  Assembly of Lemma 4.2 -/

set_option maxHeartbeats 1000000 in
theorem l42_assembly [Fintype ↥(D.S : Subgroup G)] [Fintype ↥D.B] [Fintype ↥(l42K D)]
    [Invertible (Nat.card ↥(l42K D) : ℂ)] [Invertible (Nat.card ↥D.B : ℂ)]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hc : Compat D C) (hn : D.n = 2) (β₂ : quotGroup C.P →* ℂˣ) (hβ : β₂ ≠ 1)
    (hSelm : ∀ σ : ↥(D.S : Subgroup G), σ = 1 ∨ (σ : G) = D.t ∨ (σ : G) = D.t1 ∨ (σ : G) = D.t2)
    (ht_ne_t1 : (D.t : G) ≠ D.t1) (ht_ne_t2 : (D.t : G) ≠ D.t2) (ht1_ne_t2 : D.t1 ≠ D.t2)
    {n : G} (hnN : n ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G))
    (hnt : n * D.t * n⁻¹ = D.t1) (hnt2 : n ^ 2 * D.t * (n ^ 2)⁻¹ = D.t2)
    (hcover : ∀ y ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
        y ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) ∨
        (∃ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), y = c * n) ∨
        (∃ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), y = c * n ^ 2))
    (hBN : l42NBinv D)
    (hCtriv : ∀ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), ∀ b ∈ D.B,
        ∃ b₀ ∈ D.B, c⁻¹ * b * c = b₀ * b * b₀⁻¹)
    (ν : ClassFunction ↥C.P.H0 ℂ) (hν : ν ∈ S4Index C)
    (θν θμ : ClassFunction ↥D.B ℂ) (hθν : HatOf D C ν θν) (hθμ : IsIrreducibleCharacter θμ)
    (hHatOdd : ∀ (φ θ θ' : ClassFunction ↥D.B ℂ), φ ∈ ZIrr ↥D.B → IsIrreducibleCharacter θ →
        (∀ b, AlgIntModTwo (φ b) (θ b)) → IsIrreducibleCharacter θ' →
        ∃ m : ℤ, ClassFunction.inner φ θ' = m ∧ (Odd m ↔ θ' = θ)) :
    ∃ k : ℤ, ClassFunction.inner (delta C β₂ ν) (l42muPrime D θμ) = k ∧
      (Odd k ↔ NSConj D θν θμ) := by
  classical
  have hu2 : n ^ 2 ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G) := by
    rw [pow_two]; exact Subgroup.mul_mem _ hnN hnN
  have hu3 : n ^ 3 ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G) := by
    rw [pow_succ]; exact Subgroup.mul_mem _ hu2 hnN
  have hn3C : n ^ 3 ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) :=
    l42pow3_mem D hnN hnt hnt2 ht_ne_t1 ht_ne_t2 hcover
  have hBt : ∀ b ∈ D.B, n⁻¹ * b * (n⁻¹)⁻¹ ∈ D.B := l42BNinv_swap D hBN (Subgroup.inv_mem _ hnN)
  have hBtin : ∀ b ∈ D.B, (n⁻¹)⁻¹ * b * n⁻¹ ∈ D.B := hBN n⁻¹ (Subgroup.inv_mem _ hnN)
  have hBt2 : ∀ b ∈ D.B, (n ^ 2)⁻¹ * b * ((n ^ 2)⁻¹)⁻¹ ∈ D.B :=
    l42BNinv_swap D hBN (Subgroup.inv_mem _ hu2)
  have hBt2in : ∀ b ∈ D.B, ((n ^ 2)⁻¹)⁻¹ * b * (n ^ 2)⁻¹ ∈ D.B :=
    hBN (n ^ 2)⁻¹ (Subgroup.inv_mem _ hu2)
  have hcong : ∀ b : ↥D.B, AlgIntModTwo (l42nuB D C hc ν b) (θν b) := by
    intro b
    have h := hθν.2 (l42incl D C hc b) b.2
    have h2 : (⟨l42incl D C hc b, b.2⟩ : ↥D.B) = b := Subtype.ext rfl
    rw [h2] at h
    simpa only [l42nuB_apply] using h

  set T0 : ClassFunction ↥D.B ℂ := θμ with hT0
  set T1 : ClassFunction ↥D.B ℂ := l42conjNCF D hBN n hnN θμ with hT1
  set T2 : ClassFunction ↥D.B ℂ := l42conjNCF D hBN (n ^ 2) hu2 θμ with hT2

  have hT0irr : IsIrreducibleCharacter T0 := hθμ
  have hT1irr : IsIrreducibleCharacter T1 := l42conjNCF_irreducible D hBN hnN hθμ
  have hT2irr : IsIrreducibleCharacter T2 := l42conjNCF_irreducible D hBN hu2 hθμ

  have hinner : ClassFunction.inner (delta C β₂ ν) (l42muPrime D θμ) =
      ClassFunction.inner (l42nuB D C hc ν) T0 + ClassFunction.inner (l42nuB D C hc ν) T1 +
        ClassFunction.inner (l42nuB D C hc ν) T2 := by
    rw [l42_inner_sum D C hc hn β₂ hβ hν hSelm ht_ne_t1 ht_ne_t2 ht1_ne_t2 hnt hnt2
        hBt hBt2 hBtin hBt2in θμ,
      l42conjNCF_inner D hBN hnN (l42nuB D C hc ν) θμ,
      l42conjNCF_inner D hBN hu2 (l42nuB D C hc ν) θμ,
      ← hT2, ← hT1, ← hT0]

  obtain ⟨m0, hm0, hm0o⟩ := hHatOdd (l42nuB D C hc ν) θν T0 (l42nuB_mem_ZIrr D C hc ν hν.1)
    hθν.1 hcong hT0irr
  obtain ⟨m1, hm1, hm1o⟩ := hHatOdd (l42nuB D C hc ν) θν T1 (l42nuB_mem_ZIrr D C hc ν hν.1)
    hθν.1 hcong hT1irr
  obtain ⟨m2, hm2, hm2o⟩ := hHatOdd (l42nuB D C hc ν) θν T2 (l42nuB_mem_ZIrr D C hc ν hν.1)
    hθν.1 hcong hT2irr

  have hk : ClassFunction.inner (delta C β₂ ν) (l42muPrime D θμ) = (m0 + m1 + m2 : ℤ) := by
    rw [hinner, hm0, hm1, hm2]; push_cast; ring

  have key : ∀ x y : ℤ, Odd (x + y) ↔ (Odd x ↔ ¬ Odd y) := by
    intro x y; rw [Int.odd_add, ← Int.not_odd_iff_even]
  have hsum_odd : Odd (m0 + m1 + m2) ↔
      Odd ((if T0 = θν then (1 : ℤ) else 0) + (if T1 = θν then (1 : ℤ) else 0) +
        (if T2 = θν then (1 : ℤ) else 0)) := by
    have e0 : Odd m0 ↔ Odd (if T0 = θν then (1 : ℤ) else 0) := by
      by_cases h : T0 = θν
      · rw [if_pos h, hm0o]; exact iff_of_true h (by norm_num)
      · rw [if_neg h, hm0o]; exact iff_of_false h (by norm_num)
    have e1 : Odd m1 ↔ Odd (if T1 = θν then (1 : ℤ) else 0) := by
      by_cases h : T1 = θν
      · rw [if_pos h, hm1o]; exact iff_of_true h (by norm_num)
      · rw [if_neg h, hm1o]; exact iff_of_false h (by norm_num)
    have e2 : Odd m2 ↔ Odd (if T2 = θν then (1 : ℤ) else 0) := by
      by_cases h : T2 = θν
      · rw [if_pos h, hm2o]; exact iff_of_true h (by norm_num)
      · rw [if_neg h, hm2o]; exact iff_of_false h (by norm_num)
    rw [key (m0 + m1) m2,
      key ((if T0 = θν then (1 : ℤ) else 0) + (if T1 = θν then (1 : ℤ) else 0))
        (if T2 = θν then (1 : ℤ) else 0),
      key m0 m1, key (if T0 = θν then (1 : ℤ) else 0) (if T1 = θν then (1 : ℤ) else 0)]
    tauto

  have hconjBy_iff : ∀ (x : ↥(Subgroup.normalizer ((D.S : Subgroup G) : Set G)))
      (φ ψ : ClassFunction ↥D.B ℂ),
      ConjBy D x.1 φ ψ ↔ ψ = l42conjNCF D hBN x.1⁻¹
        ((Subgroup.normalizer ((D.S : Subgroup G) : Set G)).inv_mem x.2) φ := by
    intro x φ ψ
    constructor
    · intro h
      ext b
      exact h b ⟨x.1⁻¹ * (b : G) * (x.1⁻¹)⁻¹,
        l42BNinv_swap D hBN ((Subgroup.normalizer ((D.S : Subgroup G) : Set G)).inv_mem x.2) b b.2⟩
        (by group)
    · intro h b b' hb'
      have h1 : (⟨x.1⁻¹ * (b : G) * (x.1⁻¹)⁻¹,
          l42BNinv_swap D hBN ((Subgroup.normalizer ((D.S : Subgroup G) : Set G)).inv_mem x.2)
            b b.2⟩ : ↥D.B) = b' := by
        apply Subtype.ext
        rw [hb']
        group
      calc ψ b = l42conjNCF D hBN x.1⁻¹
            ((Subgroup.normalizer ((D.S : Subgroup G) : Set G)).inv_mem x.2) φ b := by rw [h]
        _ = φ ⟨x.1⁻¹ * (b : G) * (x.1⁻¹)⁻¹,
              l42BNinv_swap D hBN ((Subgroup.normalizer ((D.S : Subgroup G) : Set G)).inv_mem x.2)
                b b.2⟩ := rfl
        _ = φ b' := congrArg φ h1
  have hNS : NSConj D θν θμ ↔ ∃ x : ↥(Subgroup.normalizer ((D.S : Subgroup G) : Set G)),
      l42conjNCF D hBN x.1 x.2 θμ = θν := by
    constructor
    · rintro ⟨x, hx, hconj⟩
      have hT : θμ = l42conjNCF D hBN x⁻¹
          ((Subgroup.normalizer ((D.S : Subgroup G) : Set G)).inv_mem hx) θν :=
        (hconjBy_iff ⟨x, hx⟩ θν θμ).mp hconj
      refine ⟨⟨x, hx⟩, ?_⟩
      rw [hT]
      rw [l42conjNCF_mul D hBN hx
        ((Subgroup.normalizer ((D.S : Subgroup G) : Set G)).inv_mem hx) θν]
      have h2 : l42conjNCF D hBN (x⁻¹ * x)
            (Subgroup.mul_mem _ ((Subgroup.normalizer ((D.S : Subgroup G) : Set G)).inv_mem hx) hx) θν
          = l42conjNCF D hBN 1 (Subgroup.one_mem _) θν :=
        l42conjNCF_congr D hBN θν
          (Subgroup.mul_mem _ ((Subgroup.normalizer ((D.S : Subgroup G) : Set G)).inv_mem hx) hx)
          (Subgroup.one_mem _) (by rw [inv_mul_cancel])
      rw [h2, l42conjNCF_zero]
    · rintro ⟨y, hy⟩
      refine ⟨y.1, y.2, ?_⟩
      rw [hconjBy_iff]
      ext b
      rw [l42conjNCF_apply]
      have h3 : l42conjNCF D hBN y.1 y.2 θμ
            (⟨y.1⁻¹ * (b : G) * y.1, hBN y.1 y.2 b b.2⟩ : ↥D.B)
          = θμ b := by
        rw [l42conjNCF_apply]
        refine congrArg θμ (Subtype.ext ?_)
        group
      rw [← h3, hy]
      refine congrArg θν (Subtype.ext ?_)
      show y.1⁻¹ * (b : G) * y.1 = y.1⁻¹ * (b : G) * (y.1⁻¹)⁻¹
      group

  have hcoverT : ∀ y : ↥(Subgroup.normalizer ((D.S : Subgroup G) : Set G)),
      l42conjNCF D hBN y.1 y.2 θμ = T0 ∨ l42conjNCF D hBN y.1 y.2 θμ = T1 ∨
        l42conjNCF D hBN y.1 y.2 θμ = T2 := by
    intro y
    rcases hcover y.1 y.2 with hc | ⟨c, hc, hceq⟩ | ⟨c, hc, hceq⟩
    · left
      rw [l42conjNCF_centralizer D hBN hCtriv hc θμ, ← hT0]
    · right; left
      rw [l42conjNCF_congr D hBN θμ y.2
          (Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer _ hc) hnN) hceq,
        l42conjNCF_centralizer_mul D hBN hCtriv hc hnN θμ, ← hT1]
    · right; right
      rw [l42conjNCF_congr D hBN θμ y.2
          (Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer _ hc) hu2) hceq,
        l42conjNCF_centralizer_mul D hBN hCtriv hc hu2 θμ, ← hT2]
  have hT1is : l42conjNCF D hBN n hnN T1 = T2 := by
    have h1 : l42conjNCF D hBN n hnN (l42conjNCF D hBN n hnN θμ) = T2 := by
      rw [l42conjNCF_mul D hBN hnN hnN θμ, hT2]
      exact l42conjNCF_congr D hBN θμ (Subgroup.mul_mem _ hnN hnN) hu2 (by rw [← pow_two])
    rwa [← hT1] at h1
  have hT2is : l42conjNCF D hBN n hnN T2 = θμ := by
    have h1 : l42conjNCF D hBN n hnN (l42conjNCF D hBN (n ^ 2) hu2 θμ) = θμ := by
      rw [l42conjNCF_mul D hBN hnN hu2 θμ]
      have h2 : l42conjNCF D hBN (n ^ 2 * n) (Subgroup.mul_mem _ hu2 hnN) θμ
          = l42conjNCF D hBN (n ^ 3) hu3 θμ :=
        l42conjNCF_congr D hBN θμ (Subgroup.mul_mem _ hu2 hnN) hu3 (by rw [← pow_succ])
      rw [h2, l42conjNCF_centralizer D hBN hCtriv hn3C θμ]
    rwa [← hT2] at h1

  have hcount : Odd ((if T0 = θν then (1 : ℤ) else 0) + (if T1 = θν then (1 : ℤ) else 0) +
      (if T2 = θν then (1 : ℤ) else 0)) ↔ NSConj D θν θμ := by
    by_cases hfix : T1 = T0
    · have hT2T0 : T2 = T0 := by
        have h1 : l42conjNCF D hBN n hnN T0 = T0 := by
          rw [hT0, ← hT1, hfix, hT0]
        rw [← hT1is, hfix]
        exact h1
      have hsum3 : (if T0 = θν then (1 : ℤ) else 0) + (if T1 = θν then (1 : ℤ) else 0) +
            (if T2 = θν then (1 : ℤ) else 0)
          = (if T0 = θν then (1 : ℤ) else 0) + (if T0 = θν then (1 : ℤ) else 0) +
            (if T0 = θν then (1 : ℤ) else 0) := by
        rw [hfix, hT2T0]
      have h3 : Odd ((if T0 = θν then (1 : ℤ) else 0) + (if T0 = θν then (1 : ℤ) else 0) +
          (if T0 = θν then (1 : ℤ) else 0)) ↔ T0 = θν := by
        by_cases h : T0 = θν
        · rw [if_pos h]
          exact iff_of_true ⟨1, by norm_num⟩ h
        · rw [if_neg h]
          exact iff_of_false (by simp) h
      have hns : NSConj D θν θμ ↔ T0 = θν := by
        rw [hNS]
        constructor
        · rintro ⟨x, hx⟩
          rcases hcoverT x with h | h | h
          · rw [h] at hx; exact hx
          · rw [h, hfix] at hx; exact hx
          · rw [h, hT2T0] at hx; exact hx
        · intro h
          refine ⟨⟨1, Subgroup.one_mem _⟩, ?_⟩
          rw [l42conjNCF_zero D hBN θμ]
          exact hT0.symm.trans h
      rw [hsum3, h3]
      exact hns.symm
    · have hT2ne0 : T2 ≠ T0 := by
        intro h
        have h1 : l42conjNCF D hBN n hnN T2 = θμ := hT2is
        rw [h, hT0, ← hT1] at h1
        exact hfix (h1.trans hT0.symm)
      have hT2ne1 : T2 ≠ T1 := by
        intro h
        have h2 : l42conjNCF D hBN n hnN T2 = T2 := by
          rw [h]
          exact hT1is.trans h
        rw [hT2is] at h2
        exact hfix (h.symm.trans (h2.symm.trans hT0.symm))
      have hcnt : Odd ((if T0 = θν then (1 : ℤ) else 0) + (if T1 = θν then (1 : ℤ) else 0) +
          (if T2 = θν then (1 : ℤ) else 0)) ↔ (T0 = θν ∨ T1 = θν ∨ T2 = θν) := by
        by_cases e0 : T0 = θν
        · have h1 : ¬ (T1 = θν) := fun h => hfix (h.trans e0.symm)
          have h2 : ¬ (T2 = θν) := fun h => hT2ne0 (h.trans e0.symm)
          rw [if_pos e0, if_neg h1, if_neg h2]
          exact iff_of_true ⟨0, by norm_num⟩ (Or.inl e0)
        · by_cases e1 : T1 = θν
          · have h2 : ¬ (T2 = θν) := fun h => hT2ne1 (h.trans e1.symm)
            rw [if_neg e0, if_pos e1, if_neg h2]
            exact iff_of_true ⟨0, by norm_num⟩ (Or.inr (Or.inl e1))
          · by_cases e2 : T2 = θν
            · rw [if_neg e0, if_neg e1, if_pos e2]
              exact iff_of_true ⟨0, by norm_num⟩ (Or.inr (Or.inr e2))
            · rw [if_neg e0, if_neg e1, if_neg e2]
              exact iff_of_false (by simp) (by tauto)
      rw [hcnt, hNS]
      constructor
      · rintro (h | h | h)
        · exact ⟨⟨1, Subgroup.one_mem _⟩, by rw [l42conjNCF_zero D hBN θμ]; exact hT0.symm.trans h⟩
        · exact ⟨⟨n, hnN⟩, by rw [← hT1]; exact h⟩
        · exact ⟨⟨n ^ 2, hu2⟩, by rw [← hT2]; exact h⟩
      · rintro ⟨x, hx⟩
        rcases hcoverT x with h | h | h
        · exact Or.inl (h ▸ hx)
        · exact Or.inr (Or.inl (h ▸ hx))
        · exact Or.inr (Or.inr (h ▸ hx))

  exact ⟨m0 + m1 + m2, hk, hsum_odd.trans hcount⟩

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
theorem lemma42 {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C23.Lemma42Prop D C := by
  intro hc hn β₂ hβ μ hμS θμ hθμ
  obtain ⟨-, hSelm, -, -, ht1ne2⟩ := l42S4grid D hn
  obtain ⟨n, hnN, -, hnt, hnt2, hcover⟩ := l42Ngrid D hn
  obtain ⟨hBN, hCtriv⟩ := l42BNinv D hn
  haveI : Fintype ↥(D.S : Subgroup G) := Fintype.ofFinite _
  haveI : Fintype ↥D.B := Fintype.ofFinite _
  haveI : Fintype ↥(l42K D) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(l42K D) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Invertible (Nat.card ↥D.B : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have ht_ne_t1 : (D.t : G) ≠ D.t1 := fun h => D.t1_nmem (h ▸ D.t_mem)
  have ht_ne_t2 : (D.t : G) ≠ D.t2 := fun h => D.t2_nmem (h ▸ D.t_mem)
  have hoddB : Odd (Nat.card ↥D.B) :=
    Odd.of_dvd_nat (odd_card_U_of_compat hc)
      (Subgroup.card_dvd_of_le (fun x hx => by rw [hc.U_eq]; exact mem_DU_of_mem_B D hx))
  refine ⟨l42muPrime D θμ, l42muPrime_mem_ZIrr D θμ hθμ.1, ?_⟩
  intro ν hνS θν hθν
  exact l42_assembly D C hc hn β₂ hβ hSelm ht_ne_t1 ht_ne_t2 ht1ne2 hnN hnt hnt2 hcover hBN
    hCtriv ν hνS θν θμ hθν hθμ.1
    (fun φ θ θ' hφ hθ hcong hθ' => l42HatOdd hoddB φ hφ θ hθ hcong θ' hθ')

end Work.BG
