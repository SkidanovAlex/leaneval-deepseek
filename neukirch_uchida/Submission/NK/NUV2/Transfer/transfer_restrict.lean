import Mathlib
import Submission.NK.NUV2.Transfer.finiteVer

/-!
# The transfer commutes with restriction along a surjection whose kernel lies in the subgroup

This file proves `NK.NUV2.Transfer.transfer_restrict`: for a surjective homomorphism
`φ : G₂ →* G₁` whose kernel is contained in a normal finite-index subgroup `H₂ ≤ G₂`, the
transfer `V_{H₂} : (G₂)ᵃᵇ → (H₂)ᵃᵇ` (also called the Verlagerung) commutes with the maps induced
by `φ` on abelianisations:

  `(φ|H₂)ᵃᵇ ∘ V_{H₂} = V_{φ(H₂)} ∘ φᵃᵇ`.

This is the classical "transfer restriction" (functoriality of the transfer along a quotient
map), cf. Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, (1.6.7) and its
consequences.

The mathematical content of the proof is the following. Choose a section `s` of the quotient
map `G₂ → G₂ ⧸ H₂` and the *compatible* section `q' ↦ Quotient.out q'` of `G₁ → G₁ ⧸ φ(H₂)`,
arranged so that `φ (s q) = Quotient.out (e q)` for the bijection `e : G₂ ⧸ H₂ ≃ G₁ ⧸ φ(H₂)`
induced by `φ`.  The transfer, computed with the transversal associated to a section `s`
(`transfer_eq_prod_section`), is the product over the cosets of `H` of
`q ↦ (s q)⁻¹ * (g * s (g⁻¹ • q))`; the two products are then compared term by term using the
equivariance `e (g • q) = φ g • e q`.
-/

open Subgroup

namespace NK.NUV2.Transfer

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

section Helper

variable {G : Type*} [Group G] {H : Subgroup G} [H.Normal]

/-- Left multiplication of the image of `g` in `G ⧸ H` is the action of `g`. -/
lemma mk_mul_smul_aux (g : G) (q : G ⧸ H) : (↑g : G ⧸ H) * q = g • q := by
  induction q using QuotientGroup.induction_on with
  | _ x => rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.mk_mul]

/-- The element attached to a section `s` of `G → G ⧸ H` at a coset `q` belongs to `H`. -/
lemma mem_sec_aux {s : G ⧸ H → G} (hs : ∀ q, (s q : G ⧸ H) = q) (g : G) (q : G ⧸ H) :
    (s q)⁻¹ * (g * s (g⁻¹ • q)) ∈ H := by
  refine QuotientGroup.eq.mp ?_
  rw [hs q, QuotientGroup.mk_mul, hs (g⁻¹ • q), mk_mul_smul_aux g (g⁻¹ • q)]
  rw [← mul_smul, mul_inv_cancel, one_smul]

/-- The transfer computed with the transversal attached to a section `s` of the quotient map. -/
lemma transfer_eq_prod_section [H.FiniteIndex] [Fintype (G ⧸ H)] {A : Type*} [CommGroup A]
    (ϕ : ↥H →* A) {s : G ⧸ H → G} (hs : ∀ q, (s q : G ⧸ H) = q) (g : G) :
    MonoidHom.transfer ϕ g =
      ∏ q : G ⧸ H, ϕ ⟨(s q)⁻¹ * (g * s (g⁻¹ • q)), mem_sec_aux hs g q⟩ := by
  rw [MonoidHom.transfer_def ϕ ⟨Set.range s, isComplement_range_left hs⟩ g]
  simp only [Subgroup.leftTransversals.diff]
  refine Finset.prod_congr (Finset.univ_congr _ _) (fun q _ => ?_)
  apply congrArg ϕ
  apply Subtype.ext
  simp only [Subtype.coe_mk]
  rw [Subgroup.IsComplement.leftQuotientEquiv_apply hs q,
    Subgroup.smul_apply_eq_smul_apply_inv_smul g ⟨Set.range s, isComplement_range_left hs⟩ q,
    smul_eq_mul, Subgroup.IsComplement.leftQuotientEquiv_apply hs (g⁻¹ • q)]

end Helper

theorem transfer_restrict {G₁ G₂ : Type*} [Group G₁] [Group G₂] [Fintype G₁] [Fintype G₂]
    (φ : G₂ →* G₁) (hφ : Function.Surjective φ) (H₂ : Subgroup G₂) [H₂.Normal] [H₂.FiniteIndex]
    [Fintype (G₂ ⧸ H₂)] [Fintype (G₁ ⧸ H₂.map φ)] (hker : φ.ker ≤ H₂) :
    ∀ x : Abelianization G₂,
      Abelianization.map ((φ.comp H₂.subtype).codRestrict (H₂.map φ) (fun h => ⟨h, h.2, rfl⟩))
          (Abelianization.lift (MonoidHom.transfer (H := H₂) (Abelianization.of : ↥H₂ →* Abelianization ↥H₂)) x)
        = Abelianization.lift (MonoidHom.transfer (H := H₂.map φ)
            (Abelianization.of : ↥(H₂.map φ) →* Abelianization ↥(H₂.map φ)))
            (Abelianization.map φ x) := by
  haveI hN : (H₂.map φ).Normal := (inferInstance : H₂.Normal).map φ hφ
  haveI hFI : (H₂.map φ).FiniteIndex := finiteIndex_of_finite_quotient (H := H₂.map φ)
  -- The bijection `e : G₂ ⧸ H₂ ≃ G₁ ⧸ φ(H₂)` induced by the surjective `φ`, whose kernel lies in `H₂`.
  let f : G₂ ⧸ H₂ →* G₁ ⧸ (H₂.map φ) :=
    QuotientGroup.map H₂ (H₂.map φ) φ (fun x hx => mem_map_of_mem φ hx)
  have hkey : ∀ y : G₂, f (QuotientGroup.mk y) = QuotientGroup.mk (φ y) :=
    fun y => QuotientGroup.map_mk H₂ (H₂.map φ) φ (fun x hx => mem_map_of_mem φ hx) y
  have hfb : Function.Bijective f := by
    constructor
    · intro a b hab
      induction a using QuotientGroup.induction_on with
      | _ x =>
        induction b using QuotientGroup.induction_on with
        | _ y =>
          rw [hkey, hkey, QuotientGroup.eq] at hab
          rw [QuotientGroup.eq]
          obtain ⟨c, hc, hc'⟩ := Subgroup.mem_map.mp hab
          have h1 : c⁻¹ * x⁻¹ * y ∈ φ.ker := by
            rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, hc']
            group
          have h2 : c⁻¹ * x⁻¹ * y ∈ H₂ := hker h1
          have h3 : c * (c⁻¹ * x⁻¹ * y) ∈ H₂ := H₂.mul_mem hc h2
          have h4 : c * (c⁻¹ * x⁻¹ * y) = x⁻¹ * y := by group
          rwa [h4] at h3
    · intro y
      induction y using QuotientGroup.induction_on with
      | _ a => exact ⟨QuotientGroup.mk (Classical.choose (hφ a)),
          by rw [hkey (Classical.choose (hφ a)), Classical.choose_spec (hφ a)]⟩
  let e : G₂ ⧸ H₂ ≃* G₁ ⧸ (H₂.map φ) := MulEquiv.ofBijective f hfb
  have hekey : ∀ y : G₂, e (QuotientGroup.mk y) = QuotientGroup.mk (φ y) := by
    intro y; rw [show e = ⇑f from rfl, hkey]
  have hesmul : ∀ (g : G₂) (q : G₂ ⧸ H₂), e (g • q) = φ g • e q := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | _ x =>
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, hekey, hekey]
      simp [MulAction.Quotient.smul_mk, smul_eq_mul, map_mul]
  -- A section `s` of `G₂ → G₂ ⧸ H₂` compatible with `Quotient.out` on the target quotient.
  let s : G₂ ⧸ H₂ → G₂ := fun q => Classical.choose (hφ (Quotient.out (e q)))
  have hsp : ∀ q, φ (s q) = Quotient.out (e q) :=
    fun q => Classical.choose_spec (hφ (Quotient.out (e q)))
  have hs : ∀ q, (s q : G₂ ⧸ H₂) = q := by
    intro q
    refine e.injective ?_
    rw [hekey, hsp q, QuotientGroup.out_eq']
  let ψ : ↥H₂ →* ↥(H₂.map φ) := (φ.comp H₂.subtype).codRestrict (H₂.map φ) (fun h => ⟨h, h.2, rfl⟩)
  have hψval : ∀ h : ↥H₂, (ψ h : G₁) = φ (h : G₂) := fun h => rfl
  let L : Abelianization G₂ →* Abelianization ↥(H₂.map φ) :=
    (Abelianization.map ψ).comp
      (Abelianization.lift (MonoidHom.transfer (H := H₂) (Abelianization.of : ↥H₂ →* Abelianization ↥H₂)))
  let R : Abelianization G₂ →* Abelianization ↥(H₂.map φ) :=
    (Abelianization.lift (MonoidHom.transfer (H := H₂.map φ)
      (Abelianization.of : ↥(H₂.map φ) →* Abelianization ↥(H₂.map φ)))).comp (Abelianization.map φ)
  have hLR : L = R := by
    refine Abelianization.hom_ext _ _ ?_
    ext g
    simp only [L, R, MonoidHom.comp_apply, Abelianization.lift_apply_of, Abelianization.map_of]
    rw [transfer_eq_prod_section (H := H₂) (Abelianization.of : ↥H₂ →* Abelianization ↥H₂) hs g,
        transfer_eq_prod_section (H := H₂.map φ)
          (Abelianization.of : ↥(H₂.map φ) →* Abelianization ↥(H₂.map φ)) Quotient.out_eq' (φ g)]
    rw [map_prod]
    refine Fintype.prod_equiv e.toEquiv _ _ (fun q => ?_)
    rw [Abelianization.map_of]
    congr 1
    apply Subtype.ext
    rw [hψval]
    change φ ((s q)⁻¹ * (g * s (g⁻¹ • q))) =
      (Quotient.out (e q))⁻¹ * (φ g * Quotient.out ((φ g)⁻¹ • e q))
    rw [map_mul, map_mul, map_inv, hsp q, ← map_inv, ← hesmul (g⁻¹) q, hsp (g⁻¹ • q)]
  exact fun x => congrFun (congrArg DFunLike.coe hLR) x

end NK.NUV2.Transfer
