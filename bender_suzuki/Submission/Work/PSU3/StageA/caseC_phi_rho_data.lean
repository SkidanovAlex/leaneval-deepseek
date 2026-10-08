import Mathlib
import Submission.Work.PSU3.StageA.caseC_module_data
import Submission.Work.PSU3.StageA.cyclic_regular_action_field

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-!
## The conjugation action of `K = Ksub H t` on `Q₀ = Q0sub H`

The two definitions below turn the conjugation map `conjQ0` of `coarseFrame_defs` into an
automorphism of `Q0sub H` and into a monoid homomorphism `Ksub H t →* MulAut (Q0sub H)`.
-/

/-- Conjugation by `k ∈ Ksub H t` as an automorphism of `Q0sub H`. -/
noncomputable def conjQ0Aut (H : Subgroup G) (t : G) (k : ↥(Work.ThmF.Ksub H t)) :
    MulAut ↥(Work.ThmF.Q0sub H) where
  toFun := conjQ0 H t k
  invFun := conjQ0 H t k⁻¹
  left_inv y := by
    apply Subtype.ext
    simp only [conjQ0_coe, Subgroup.coe_inv]
    group
  right_inv y := by
    apply Subtype.ext
    simp only [conjQ0_coe, Subgroup.coe_inv]
    group
  map_mul' x y := by
    apply Subtype.ext
    simp only [conjQ0_coe, Subgroup.coe_mul]
    group

@[simp] theorem conjQ0Aut_apply (k : ↥(Work.ThmF.Ksub H t)) (y : ↥(Work.ThmF.Q0sub H)) :
    conjQ0Aut H t k y = conjQ0 H t k y := rfl

/-- The conjugation action `Ksub H t →* MulAut (Q0sub H)`. -/
noncomputable def conjQ0Hom (H : Subgroup G) (t : G) :
    ↥(Work.ThmF.Ksub H t) →* MulAut ↥(Work.ThmF.Q0sub H) where
  toFun := conjQ0Aut H t
  map_one' := by
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    simp only [conjQ0Aut_apply, conjQ0_coe, Subgroup.coe_one, one_mul, inv_one, mul_one,
      MulAut.one_apply]
  map_mul' k₁ k₂ := by
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    simp only [conjQ0Aut_apply, conjQ0_coe, Subgroup.coe_mul, MulAut.mul_apply]
    group

@[simp] theorem conjQ0Hom_apply (k : ↥(Work.ThmF.Ksub H t)) (y : ↥(Work.ThmF.Q0sub H)) :
    conjQ0Hom H t k y = conjQ0 H t k y := rfl

/-! ## The field structure and the character `ρ` on `Q₀ = ⟨Inv H⟩` -/

/-- **Peterfalvi II, Ch. V §1 Prop. 3** (the `K`-part, with `W ≠ 1`): `Q₀ = ⟨Inv H⟩` carries a
field structure `F` of order `q = |Q₀|` whose addition is the group law of `Q₀` (so that
`Q₀ ≅ (F,+)`) and on which `K = Ksub H t` acts by multiplication through a homomorphism
`ρ : K →* Fˣ`.

This is the `φ`/`ρ` half of `CaseCModuleData`: `K` is cyclic of order `q - 1`
(`caseC_gen`, `caseC_card_Ksub`) and acts regularly on the `q - 1` involutions of `H`
(`caseC_reg`), i.e. as a Singer cycle on the `𝔽₂`-space `Q₀`; that is the content of
`cyclic_regular_action_field`. -/
theorem caseC_phi_rho_data {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hWne : Work.ThmF.W H t ≠ ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥(Work.ThmF.Q0sub H) → F)
      (ρ : ↥(Work.ThmF.Ksub H t) →* Fˣ),
      Nat.card F = Nat.card ↥(Work.ThmF.Q0sub H) ∧ Function.Bijective φ ∧
      (∀ a b : ↥(Work.ThmF.Q0sub H), φ (a * b) = φ a + φ b) ∧
      (∀ (k : ↥(Work.ThmF.Ksub H t)) (y : ↥(Work.ThmF.Q0sub H)),
        φ (Work.PSU3.StageA.conjQ0 H t k y) = (ρ k : F) * φ y) := by
  classical
  -- the generator of `Ksub H t`
  let k₀ : ↥(Work.ThmF.Ksub H t) := caseC_gen hS hC4 hWne
  -- cardinalities
  have hcardQ : Nat.card ↥(Work.ThmF.Q0sub H) = (involutions (H : Set G)).ncard + 1 :=
    caseC_card_Q0sub_eq hS hC4
  have hcardK : Nat.card ↥(Work.ThmF.Ksub H t) = (involutions (H : Set G)).ncard :=
    caseC_card_Ksub hS hC4 hWne
  have hcard2 : 1 < Nat.card ↥(Work.ThmF.Q0sub H) := by
    obtain ⟨n, hn2, hn⟩ := caseC_Q0sub_card hS hC4 hWne
    rw [hn]
    calc (1 : ℕ) < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  -- a non-identity element `e` of `Q₀` (then automatically an involution of `H`)
  obtain ⟨e, he1⟩ : ∃ e : ↥(Work.ThmF.Q0sub H), e ≠ 1 := by
    by_contra h
    push_neg at h
    have hsub : Subsingleton ↥(Work.ThmF.Q0sub H) := ⟨fun a b => by rw [h a, h b]⟩
    have hone : Nat.card ↥(Work.ThmF.Q0sub H) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    omega
  have he_inv : (e : G) ∈ involutions (H : Set G) := by
    have hmem : (e : G) ∈ Work.ThmF.Q0 H := by
      rw [← caseC_Q0sub_eq_Q0 hS hC4]; exact e.2
    rcases (Work.ThmF.mem_Q0_iff.mp hmem) with h | h
    · exact h
    · exact absurd (Subtype.ext h) he1
  -- `Q₀` has exponent two
  have h2 : ∀ x : ↥(Work.ThmF.Q0sub H), x * x = 1 := by
    intro x
    apply Subtype.ext
    show (x : G) * (x : G) = (1 : G)
    exact caseC_mem_Q0sub_iff hS hC4 (x : G) x.2
  have hgenpos : 0 < orderOf k₀ := by
    rw [show orderOf k₀ = Nat.card ↥(Work.ThmF.Ksub H t) from caseC_gen_orderOf hS hC4 hWne]
    exact Nat.card_pos
  -- every element of `Ksub H t` is a power of the generator
  have hspan : ∀ k : ↥(Work.ThmF.Ksub H t),
      ∃ j : ℕ, conjQ0Hom H t k = conjQ0Hom H t k₀ ^ j := by
    intro k
    have hmem : k ∈ Subgroup.zpowers k₀ := by
      rw [show Subgroup.zpowers k₀ = ⊤ from caseC_gen_spec hS hC4 hWne]
      exact Subgroup.mem_top k
    obtain ⟨j, hj⟩ := pow_eq_of_mem_zpowers hgenpos hmem
    exact ⟨j, by rw [← hj, map_pow]⟩
  -- `K` acts faithfully
  have hKset_mem : ∀ k : ↥(Work.ThmF.Ksub H t), (k : G) ∈ Work.ThmF.Kset H t := by
    intro k
    rw [← (caseC_Ksub_cyc hS hC4 hWne).1]
    exact k.2
  have hinj : Function.Injective (conjQ0Hom H t) := by
    intro k₁ k₂ h12
    have hev : conjQ0 H t k₁ e = conjQ0 H t k₂ e := by
      have h := congrArg (fun (f : MulAut ↥(Work.ThmF.Q0sub H)) => f e) h12
      simpa only [conjQ0Hom_apply] using h
    have hev' : (k₁ : G) * (e : G) * (k₁ : G)⁻¹ = (k₂ : G) * (e : G) * (k₂ : G)⁻¹ := by
      have h := congrArg (fun (y : ↥(Work.ThmF.Q0sub H)) => (y : G)) hev
      simpa only [conjQ0_coe] using h
    -- the stabiliser of `e` in `Kset H t` is trivial, so `k₁⁻¹ * k₂` fixes `e`
    obtain ⟨k, -, huniq⟩ := (caseC_reg hS hC4) (e : G) he_inv (e : G) he_inv
    have hk1 : k = 1 := (huniq 1 ⟨Work.ThmF.one_mem_Kset H t, by simp⟩).symm
    have hconj : ((k₁ : G)⁻¹ * (k₂ : G)) * (e : G) * ((k₁ : G)⁻¹ * (k₂ : G))⁻¹ = (e : G) := by
      have h1 : (k₂ : G) * (e : G) * (k₂ : G)⁻¹ = (k₁ : G) * (e : G) * (k₁ : G)⁻¹ := hev'.symm
      calc ((k₁ : G)⁻¹ * (k₂ : G)) * (e : G) * ((k₁ : G)⁻¹ * (k₂ : G))⁻¹
          = (k₁ : G)⁻¹ * ((k₂ : G) * (e : G) * (k₂ : G)⁻¹) * (k₁ : G) := by group
        _ = (k₁ : G)⁻¹ * ((k₁ : G) * (e : G) * (k₁ : G)⁻¹) * (k₁ : G) := by rw [h1]
        _ = (e : G) := by group
    have hcoe : ((k₁⁻¹ * k₂ : ↥(Work.ThmF.Ksub H t)) : G) = (k₁ : G)⁻¹ * (k₂ : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hfix : ((k₁⁻¹ * k₂ : ↥(Work.ThmF.Ksub H t)) : G) = 1 := by
      have h := huniq ((k₁⁻¹ * k₂ : ↥(Work.ThmF.Ksub H t)) : G)
        ⟨hKset_mem _, by rw [hcoe]; exact hconj⟩
      rw [hk1] at h
      exact h
    have hprod : k₁⁻¹ * k₂ = (1 : ↥(Work.ThmF.Ksub H t)) := Subtype.ext hfix
    have := congrArg (fun x : ↥(Work.ThmF.Ksub H t) => k₁ * x) hprod
    simpa using this.symm
  have hord : orderOf (conjQ0Hom H t k₀) = Nat.card ↥(Work.ThmF.Q0sub H) - 1 := by
    rw [orderOf_injective (conjQ0Hom H t) hinj k₀,
      show orderOf k₀ = Nat.card ↥(Work.ThmF.Ksub H t) from caseC_gen_orderOf hS hC4 hWne,
      hcardK, hcardQ]
    omega
  -- `K` acts transitively on the non-identity elements of `Q₀`
  have htrans : ∀ v : ↥(Work.ThmF.Q0sub H), v ≠ 1 →
      ∃ i : ℕ, ((conjQ0Hom H t k₀) ^ i) e = v := by
    intro v hv
    have hv_inv : (v : G) ∈ involutions (H : Set G) := by
      have hmem : (v : G) ∈ Work.ThmF.Q0 H := by
        rw [← caseC_Q0sub_eq_Q0 hS hC4]; exact v.2
      rcases (Work.ThmF.mem_Q0_iff.mp hmem) with h | h
      · exact h
      · exact absurd (Subtype.ext h) hv
    obtain ⟨k, ⟨hkKset, hk⟩, -⟩ :=
      (caseC_reg hS hC4) (e : G) he_inv (v : G) hv_inv
    have hkKsub : k ∈ Work.ThmF.Ksub H t := by
      have h1 : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
        (caseC_Ksub_cyc hS hC4 hWne).1
      have hk : k ∈ (Work.ThmF.Ksub H t : Set G) := by rw [h1]; exact hkKset
      exact hk
    let k' : ↥(Work.ThmF.Ksub H t) := ⟨k, hkKsub⟩
    have hmem : k' ∈ Subgroup.zpowers k₀ := by
      rw [show Subgroup.zpowers k₀ = ⊤ from caseC_gen_spec hS hC4 hWne]
      exact Subgroup.mem_top k'
    obtain ⟨j, hj⟩ := pow_eq_of_mem_zpowers hgenpos hmem
    refine ⟨j, ?_⟩
    rw [← map_pow, hj]
    apply Subtype.ext
    rw [conjQ0Hom_apply, conjQ0_coe]
    exact hk
  -- the abstract Singer-cycle construction
  haveI hFinQ : Fintype ↥(Work.ThmF.Q0sub H) := Fintype.ofFinite _
  obtain ⟨F, hF, hFintype, φ, ρ, hcardF, hadd, hequiv⟩ :=
    cyclic_regular_action_field h2 (conjQ0Hom H t) k₀ e he1 hspan hord htrans
  exact ⟨F, hF, hFintype, ⇑φ, ρ, hcardF, φ.bijective, fun a b => hadd a b,
    fun k y => by simpa only [conjQ0Hom_apply] using hequiv k y⟩

end Work.PSU3.StageA
