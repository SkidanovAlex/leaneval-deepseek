import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.SSGRoute.PT.H2Transfer
import Submission.Work.SSGRoute.kummerBase_euler_h3_absKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transfer of `H³` along a homeomorphic isomorphism of Galois groups

The workspace's continuous cohomology `Work.SSGRoute.H3 G M` is the quotient of the locally
constant `3`-cocycles `Z3 G M` by the `3`-coboundaries `B3 G M = d²(C²_c)`.

For a group isomorphism `Φ : G' ≃* G` which is moreover a **homeomorphism** and a compatible
coefficient isomorphism `Ψ : M' ≃+ M` (`Ψ (g' • m') = Φ g' • Ψ m'`), the assignment

  `c ↦ (fun p => Ψ (c (Φ.symm p.1, Φ.symm p.2.1, Φ.symm p.2.2)))`

transfers locally constant `3`-cochains, `3`-cocycles and `3`-coboundaries (the transfer is
compatible with `d²`), and hence descends to

  `Work.SSGRoute.PT.h3Transfer Φ hΦ Ψ hΨ : H3 G' M' ≃+ H3 G M`.

This is the degree-`3` companion of `Work.SSGRoute.PT.h1Transfer` and
`Work.SSGRoute.PT.h2Transfer`.
-/

open scoped Classical
open Work.AbsoluteKummer

namespace Work.SSGRoute.PT

noncomputable section

variable {G G' : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']

variable {M M' : Type*} [AddCommGroup M] [DistribMulAction G M]
  [AddCommGroup M'] [DistribMulAction G' M']

/-- **The `3`-cochain transfer** along `Φ : G' ≃* G` and `Ψ : M' ≃+ M`:
`c ↦ (fun p => Ψ (c (Φ.symm p.1, Φ.symm p.2.1, Φ.symm p.2.2)))`. -/
noncomputable def cochainTransfer3 (Φ : G' ≃* G) (Ψ : M' ≃+ M) :
    (G' × G' × G' → M') →+ (G × G × G → M) where
  toFun c p := Ψ (c (Φ.symm p.1, Φ.symm p.2.1, Φ.symm p.2.2))
  map_zero' := by funext p; simp
  map_add' c d := by funext p; simp only [Pi.add_apply, map_add]

@[simp] theorem cochainTransfer3_apply (Φ : G' ≃* G) (Ψ : M' ≃+ M) (c : G' × G' × G' → M')
    (p : G × G × G) :
    cochainTransfer3 Φ Ψ c p = Ψ (c (Φ.symm p.1, Φ.symm p.2.1, Φ.symm p.2.2)) := rfl

/-- Scalar multiplication by `g : G` on the image of `Ψ` is `Ψ` of `Φ.symm g • ·`. -/
theorem hΨ_symm (Φ : G' ≃* G) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') :
    ∀ (g : G) (m' : M'), g • Ψ m' = Ψ (Φ.symm g • m') := by
  intro g m'
  have h : g • Ψ m' = Φ (Φ.symm g) • Ψ m' := by rw [MulEquiv.apply_symm_apply]
  rw [h, hΨ]

/-- The map `p ↦ (Φ.symm p.1, Φ.symm p.2.1, Φ.symm p.2.2)` is continuous when `Φ.symm` is. -/
theorem continuous_triplePreimage (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G')) :
    Continuous (fun p : G × G × G => (Φ.symm p.1, Φ.symm p.2.1, Φ.symm p.2.2)) :=
  (hΦc.comp continuous_fst).prodMk
    ((hΦc.comp continuous_snd.fst).prodMk (hΦc.comp continuous_snd.snd))

/-- The transfer of a locally constant `3`-cochain is locally constant. -/
theorem cochainTransfer3_isLocallyConstant (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) {c : G' × G' × G' → M'} (hc : Work.AbsoluteKummer.IsLocallyConstant c) :
    Work.AbsoluteKummer.IsLocallyConstant (cochainTransfer3 Φ Ψ c) :=
  (isLocallyConstant_comp_continuous hc (continuous_triplePreimage Φ hΦc)).map (Ψ : M' → M)

/-- The `3`-cochain transfer intertwines `d³` with the coefficient isomorphism `Ψ`:
`d³ (Ψ ∘ c ∘ Φ.symm) = Ψ ∘ d³ c ∘ Φ.symm`. -/
theorem d3_cochainTransfer3 (Φ : G' ≃* G) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (c : G' × G' × G' → M') (p : G × G × G × G) :
    d3 (G := G) (A := M) (cochainTransfer3 Φ Ψ c) p
      = Ψ (d3 (G := G') (A := M') c
          (Φ.symm p.1, Φ.symm p.2.1, Φ.symm p.2.2.1, Φ.symm p.2.2.2)) := by
  obtain ⟨g, h, k, l⟩ := p
  rw [d3_apply, d3_apply]
  simp only [cochainTransfer3_apply, map_sub, map_add]
  rw [hΨ_symm Φ Ψ hΨ g (c (Φ.symm h, Φ.symm k, Φ.symm l))]
  simp only [map_mul]

/-- The transfer of a `3`-cocycle is a `3`-cocycle. -/
theorem cochainTransfer3_mem_Z3 (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    {c : G' × G' × G' → M'} (hc : c ∈ Z3 (M := M') G') :
    cochainTransfer3 Φ Ψ c ∈ Z3 (M := M) G := by
  rw [mem_Z3_iff] at hc ⊢
  obtain ⟨hcocyc, hclc⟩ := hc
  refine ⟨?_, cochainTransfer3_isLocallyConstant Φ hΦc Ψ hclc⟩
  funext p
  rw [d3_cochainTransfer3 Φ Ψ hΨ c p]
  exact (congrArg Ψ (congrFun hcocyc _)).trans (map_zero Ψ)

/-- The `3`-cochain transfer intertwines `d²` with the `2`-cochain transfer. -/
theorem cochainTransfer3_d2 (Φ : G' ≃* G) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') (c : G' × G' → M') :
    cochainTransfer3 Φ Ψ (Work.GroupCohomology.d2 G' M' c) =
      Work.GroupCohomology.d2 G M (cochainTransfer2 Φ Ψ c) := by
  funext p
  obtain ⟨g, h, k⟩ := p
  rw [cochainTransfer3_apply, Work.GroupCohomology.d2_apply, Work.GroupCohomology.d2_apply]
  simp only [cochainTransfer2_apply, map_sub, map_add]
  rw [hΨ_symm Φ Ψ hΨ g (c (Φ.symm h, Φ.symm k))]
  simp only [map_mul]

/-- The transfer sends `3`-coboundaries to `3`-coboundaries. -/
theorem cochainTransfer3_mem_B3 (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    {c : G' × G' × G' → M'} (hc : c ∈ B3 (M := M') G') :
    cochainTransfer3 Φ Ψ c ∈ B3 (M := M) G := by
  rw [mem_B3_iff] at hc ⊢
  obtain ⟨b, hb, rfl⟩ := hc
  exact ⟨cochainTransfer2 Φ Ψ b, cochainTransfer2_isLocallyConstant Φ hΦc Ψ hb,
    (cochainTransfer3_d2 Φ Ψ hΨ b).symm⟩

/-- **The transfer on continuous `3`-cocycles.** -/
noncomputable def z3Transfer (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') :
    Z3 (M := M') G' →+ Z3 (M := M) G where
  toFun c := ⟨cochainTransfer3 Φ Ψ (c : G' × G' × G' → M'),
    cochainTransfer3_mem_Z3 Φ hΦc Ψ hΨ c.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _c _d := Subtype.ext (map_add _ _ _)

@[simp] theorem z3Transfer_coe (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (c : Z3 (M := M') G') :
    ((z3Transfer Φ hΦc Ψ hΨ c : Z3 (M := M) G) : G × G × G → M)
      = cochainTransfer3 Φ Ψ (c : G' × G' × G' → M') := rfl

/-- **The transfer on `H³`**, as an additive homomorphism. -/
noncomputable def h3TransferAddHom (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') :
    H3 (M := M') G' →+ H3 (M := M) G :=
  QuotientAddGroup.lift ((B3 (M := M') G').comap (Z3 (M := M') G').subtype)
    ((H3π (M := M) G).comp (z3Transfer Φ hΦc Ψ hΨ)) (by
      intro x hx
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, H3π_eq_zero_iff, z3Transfer_coe]
      have hx' : (x : G' × G' × G' → M') ∈ B3 (M := M') G' := AddSubgroup.mem_comap.mp hx
      exact cochainTransfer3_mem_B3 Φ hΦc Ψ hΨ hx')

theorem h3TransferAddHom_mk (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (c : Z3 (M := M') G') :
    h3TransferAddHom Φ hΦc Ψ hΨ (H3π (M := M') G' c) =
      H3π (M := M) G (z3Transfer Φ hΦc Ψ hΨ c) :=
  QuotientAddGroup.lift_mk' _ _ c

/-- The two `3`-cochain transfers are inverse to each other. -/
theorem cochainTransfer3_symm_comp (Φ : G' ≃* G) (Ψ : M' ≃+ M) (c : G' × G' × G' → M') :
    cochainTransfer3 Φ.symm Ψ.symm (cochainTransfer3 Φ Ψ c) = c := by
  funext p
  obtain ⟨a, b, d⟩ := p
  simp only [cochainTransfer3_apply, MulEquiv.symm_symm, MulEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply]

/-- The two `3`-cochain transfers are inverse to each other, in the other order. -/
theorem cochainTransfer3_comp_symm (Φ : G' ≃* G) (Ψ : M' ≃+ M) (c : G × G × G → M) :
    cochainTransfer3 Φ Ψ (cochainTransfer3 Φ.symm Ψ.symm c) = c := by
  funext p
  obtain ⟨a, b, d⟩ := p
  simp only [cochainTransfer3_apply, MulEquiv.symm_symm, MulEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

/-- The transfer along `Φ` followed by the transfer along `Φ.symm` is the identity. -/
theorem h3TransferAddHom_leftInverse (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (hΦc' : Continuous (Φ : G' → G)) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') (x : H3 (M := M') G') :
    h3TransferAddHom Φ.symm (by simpa using hΦc') Ψ.symm (symm_compat Φ Ψ hΨ)
      (h3TransferAddHom Φ hΦc Ψ hΨ x) = x := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((B3 (M := M') G').comap (Z3 (M := M') G').subtype) x
  rw [← hc]
  change h3TransferAddHom Φ.symm (by simpa using hΦc') Ψ.symm (symm_compat Φ Ψ hΨ)
      (h3TransferAddHom Φ hΦc Ψ hΨ (H3π (M := M') G' c)) = H3π (M := M') G' c
  rw [h3TransferAddHom_mk, h3TransferAddHom_mk,
    congrArg (H3π (M := M') G')
      (Subtype.ext (cochainTransfer3_symm_comp Φ Ψ (c : G' × G' × G' → M')))]

/-- The transfer along `Φ.symm` followed by the transfer along `Φ` is the identity. -/
theorem h3TransferAddHom_rightInverse (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (hΦc' : Continuous (Φ : G' → G)) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') (y : H3 (M := M) G) :
    h3TransferAddHom Φ hΦc Ψ hΨ
      (h3TransferAddHom Φ.symm (by simpa using hΦc') Ψ.symm (symm_compat Φ Ψ hΨ) y) = y := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((B3 (M := M) G).comap (Z3 (M := M) G).subtype) y
  rw [← hc]
  change h3TransferAddHom Φ hΦc Ψ hΨ
      (h3TransferAddHom Φ.symm (by simpa using hΦc') Ψ.symm (symm_compat Φ Ψ hΨ)
        (H3π (M := M) G c)) = H3π (M := M) G c
  rw [h3TransferAddHom_mk, h3TransferAddHom_mk,
    congrArg (H3π (M := M) G)
      (Subtype.ext (cochainTransfer3_comp_symm Φ Ψ (c : G × G × G → M)))]

/-- **Transfer of `H³` along a homeomorphic group isomorphism with compatible coefficients.** -/
noncomputable def h3Transfer (Φ : G' ≃* G) (hΦ : IsHomeomorph (Φ : G' → G))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') :
    H3 (M := M') G' ≃+ H3 (M := M) G where
  toFun := h3TransferAddHom Φ (continuous_symm_of_isHomeomorph_mulEquiv Φ hΦ) Ψ hΨ
  invFun := h3TransferAddHom Φ.symm (by simpa using hΦ.continuous) Ψ.symm
    (symm_compat Φ Ψ hΨ)
  left_inv := h3TransferAddHom_leftInverse Φ
    (continuous_symm_of_isHomeomorph_mulEquiv Φ hΦ) hΦ.continuous Ψ hΨ
  right_inv := h3TransferAddHom_rightInverse Φ
    (continuous_symm_of_isHomeomorph_mulEquiv Φ hΦ) hΦ.continuous Ψ hΨ
  map_add' := map_add _

theorem H3Transfer {G G' : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    {M M' : Type*} [AddCommGroup M] [DistribMulAction G M]
    [AddCommGroup M'] [DistribMulAction G' M']
    (Φ : G' ≃* G) (hΦ : IsHomeomorph (Φ : G' → G)) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') :
    Nonempty (Work.SSGRoute.H3 (M := M') G' ≃+ Work.SSGRoute.H3 (M := M) G) :=
  ⟨h3Transfer Φ hΦ Ψ hΨ⟩

end

end Work.SSGRoute.PT
