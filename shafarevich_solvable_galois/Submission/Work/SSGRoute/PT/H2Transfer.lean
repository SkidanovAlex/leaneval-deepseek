import Mathlib
import Submission.Work.SSGRoute.PT.H1Transfer
import Submission.Work.AbsoluteKummer.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transfer of `H²` along a homeomorphic isomorphism of Galois groups

The workspace's continuous cohomology `Work.AbsoluteKummer.H2 G M` is the quotient of the locally
constant `2`-cocycles `Z2 G M` by the `2`-coboundaries `B2 G M = d¹(C¹_c)`.

For a group isomorphism `Φ : G' ≃* G` which is moreover a **homeomorphism** and a compatible
coefficient isomorphism `Ψ : M' ≃+ M` (`Ψ (g' • m') = Φ g' • Ψ m'`), the assignment

  `c ↦ (fun p => Ψ (c (Φ.symm p.1, Φ.symm p.2)))`

transfers locally constant `2`-cochains, `2`-cocycles and `2`-coboundaries (the transfer is
compatible with `d¹`), and hence descends to

  `Work.SSGRoute.PT.h2Transfer Φ hΦ Ψ hΨ : H2 G' M' ≃+ H2 G M`.

This is the degree-`2` companion of `Work.SSGRoute.PT.h1Transfer`.
-/

open scoped Classical
open Work.AbsoluteKummer

namespace Work.SSGRoute.PT

noncomputable section

variable {G G' : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']

variable {M M' : Type*} [AddCommGroup M] [DistribMulAction G M]
  [AddCommGroup M'] [DistribMulAction G' M']

/-- **The `2`-cochain transfer** along `Φ : G' ≃* G` and `Ψ : M' ≃+ M`:
`c ↦ (fun p => Ψ (c (Φ.symm p.1, Φ.symm p.2)))`. -/
noncomputable def cochainTransfer2 (Φ : G' ≃* G) (Ψ : M' ≃+ M) :
    (G' × G' → M') →+ (G × G → M) where
  toFun c p := Ψ (c (Φ.symm p.1, Φ.symm p.2))
  map_zero' := by funext p; simp
  map_add' c d := by funext p; simp only [Pi.add_apply, map_add]

@[simp] theorem cochainTransfer2_apply (Φ : G' ≃* G) (Ψ : M' ≃+ M) (c : G' × G' → M')
    (p : G × G) : cochainTransfer2 Φ Ψ c p = Ψ (c (Φ.symm p.1, Φ.symm p.2)) := rfl

/-- The map `p ↦ (Φ.symm p.1, Φ.symm p.2)` is continuous when `Φ.symm` is. -/
theorem continuous_pairPreimage (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G')) :
    Continuous (fun p : G × G => (Φ.symm p.1, Φ.symm p.2)) :=
  (hΦc.comp continuous_fst).prodMk (hΦc.comp continuous_snd)

/-- The transfer of a locally constant `2`-cochain is locally constant. -/
theorem cochainTransfer2_isLocallyConstant (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) {c : G' × G' → M'} (hc : Work.AbsoluteKummer.IsLocallyConstant c) :
    Work.AbsoluteKummer.IsLocallyConstant (cochainTransfer2 Φ Ψ c) :=
  (isLocallyConstant_comp_continuous hc (continuous_pairPreimage Φ hΦc)).map (Ψ : M' → M)

/-- The transfer of a `2`-cocycle is a `2`-cocycle. -/
theorem cochainTransfer2_mem_Z2 (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    {c : G' × G' → M'} (hc : c ∈ Z2 G' M') : cochainTransfer2 Φ Ψ c ∈ Z2 G M := by
  rw [mem_Z2_iff] at hc ⊢
  obtain ⟨hcocyc, hclc⟩ := hc
  refine ⟨?_, cochainTransfer2_isLocallyConstant Φ hΦc Ψ hclc⟩
  intro g h k
  have h1 : Φ.symm (g * h) = Φ.symm g * Φ.symm h := map_mul _ _ _
  have h2 : Φ.symm (h * k) = Φ.symm h * Φ.symm k := map_mul _ _ _
  have key := hcocyc (Φ.symm g) (Φ.symm h) (Φ.symm k)
  simp only [cochainTransfer2_apply]
  rw [h1, h2, ← map_add, key, map_add, hΨ, MulEquiv.apply_symm_apply]

/-- The `2`-cochain transfer intertwines the coboundary `d¹` with the `1`-cochain transfer. -/
theorem cochainTransfer2_d1 (Φ : G' ≃* G) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') (f : G' → M') :
    cochainTransfer2 Φ Ψ (Work.GroupCohomology.d1 G' M' f) =
      Work.GroupCohomology.d1 G M (cochainTransfer Φ Ψ f) := by
  funext p
  obtain ⟨g, h⟩ := p
  simp only [cochainTransfer2_apply, cochainTransfer_apply, Work.GroupCohomology.d1_apply,
    map_sub, map_add]
  rw [hΨ, map_mul, MulEquiv.apply_symm_apply]

/-- The transfer sends `2`-coboundaries to `2`-coboundaries. -/
theorem cochainTransfer2_mem_B2 (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    {c : G' × G' → M'} (hc : c ∈ B2 G' M') : cochainTransfer2 Φ Ψ c ∈ B2 G M := by
  rw [mem_B2_iff] at hc ⊢
  obtain ⟨f, hf, rfl⟩ := hc
  exact ⟨cochainTransfer Φ Ψ f, cochainTransfer_isLocallyConstant Φ hΦc Ψ hf,
    (cochainTransfer2_d1 Φ Ψ hΨ f).symm⟩

/-- **The transfer on continuous `2`-cocycles.** -/
noncomputable def z2Transfer (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') :
    Z2 G' M' →+ Z2 G M where
  toFun c := ⟨cochainTransfer2 Φ Ψ (c : G' × G' → M'),
    cochainTransfer2_mem_Z2 Φ hΦc Ψ hΨ c.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _c _d := Subtype.ext (map_add _ _ _)

@[simp] theorem z2Transfer_coe (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (c : Z2 G' M') :
    ((z2Transfer Φ hΦc Ψ hΨ c : Z2 G M) : G × G → M)
      = cochainTransfer2 Φ Ψ (c : G' × G' → M') := rfl

/-- **The transfer on `H²`**, as an additive homomorphism. -/
noncomputable def h2TransferAddHom (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') :
    H2 G' M' →+ H2 G M :=
  QuotientAddGroup.lift ((B2 G' M').comap (Z2 G' M').subtype)
    ((H2π G M).comp (z2Transfer Φ hΦc Ψ hΨ)) (by
      intro x hx
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, H2π_eq_zero_iff, z2Transfer_coe]
      have hx' : (x : G' × G' → M') ∈ B2 G' M' := AddSubgroup.mem_comap.mp hx
      exact cochainTransfer2_mem_B2 Φ hΦc Ψ hΨ hx')

theorem h2TransferAddHom_mk (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (c : Z2 G' M') :
    h2TransferAddHom Φ hΦc Ψ hΨ (H2π G' M' c) = H2π G M (z2Transfer Φ hΦc Ψ hΨ c) :=
  QuotientAddGroup.lift_mk' _ _ c

/-- The two cochain transfers are inverse to each other. -/
theorem cochainTransfer2_symm_comp (Φ : G' ≃* G) (Ψ : M' ≃+ M) (c : G' × G' → M') :
    cochainTransfer2 Φ.symm Ψ.symm (cochainTransfer2 Φ Ψ c) = c := by
  funext p
  obtain ⟨a, b⟩ := p
  simp only [cochainTransfer2_apply, MulEquiv.symm_symm, MulEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply]

/-- The two cochain transfers are inverse to each other, in the other order. -/
theorem cochainTransfer2_comp_symm (Φ : G' ≃* G) (Ψ : M' ≃+ M) (c : G × G → M) :
    cochainTransfer2 Φ Ψ (cochainTransfer2 Φ.symm Ψ.symm c) = c := by
  funext p
  obtain ⟨a, b⟩ := p
  simp only [cochainTransfer2_apply, MulEquiv.symm_symm, MulEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

/-- The transfer along `Φ` followed by the transfer along `Φ.symm` is the identity. -/
theorem h2TransferAddHom_leftInverse (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (hΦc' : Continuous (Φ : G' → G)) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') (x : H2 G' M') :
    h2TransferAddHom Φ.symm (by simpa using hΦc') Ψ.symm (symm_compat Φ Ψ hΨ)
      (h2TransferAddHom Φ hΦc Ψ hΨ x) = x := by
  obtain ⟨c, hc⟩ :=
    QuotientAddGroup.mk'_surjective ((B2 G' M').comap (Z2 G' M').subtype) x
  rw [← hc]
  change h2TransferAddHom Φ.symm (by simpa using hΦc') Ψ.symm (symm_compat Φ Ψ hΨ)
      (h2TransferAddHom Φ hΦc Ψ hΨ (H2π G' M' c)) = H2π G' M' c
  rw [h2TransferAddHom_mk, h2TransferAddHom_mk,
    congrArg (H2π G' M') (Subtype.ext (cochainTransfer2_symm_comp Φ Ψ (c : G' × G' → M')))]

/-- The transfer along `Φ.symm` followed by the transfer along `Φ` is the identity. -/
theorem h2TransferAddHom_rightInverse (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (hΦc' : Continuous (Φ : G' → G)) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') (y : H2 G M) :
    h2TransferAddHom Φ hΦc Ψ hΨ
      (h2TransferAddHom Φ.symm (by simpa using hΦc') Ψ.symm (symm_compat Φ Ψ hΨ) y) = y := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective ((B2 G M).comap (Z2 G M).subtype) y
  rw [← hc]
  change h2TransferAddHom Φ hΦc Ψ hΨ
      (h2TransferAddHom Φ.symm (by simpa using hΦc') Ψ.symm (symm_compat Φ Ψ hΨ)
        (H2π G M c)) = H2π G M c
  rw [h2TransferAddHom_mk, h2TransferAddHom_mk,
    congrArg (H2π G M) (Subtype.ext (cochainTransfer2_comp_symm Φ Ψ (c : G × G → M)))]

/-- **Transfer of `H²` along a homeomorphic group isomorphism with compatible coefficients.** -/
noncomputable def h2Transfer (Φ : G' ≃* G) (hΦ : IsHomeomorph (Φ : G' → G))
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') :
    H2 G' M' ≃+ H2 G M where
  toFun := h2TransferAddHom Φ (continuous_symm_of_isHomeomorph_mulEquiv Φ hΦ) Ψ hΨ
  invFun := h2TransferAddHom Φ.symm (by simpa using hΦ.continuous) Ψ.symm
    (symm_compat Φ Ψ hΨ)
  left_inv := h2TransferAddHom_leftInverse Φ
    (continuous_symm_of_isHomeomorph_mulEquiv Φ hΦ) hΦ.continuous Ψ hΨ
  right_inv := h2TransferAddHom_rightInverse Φ
    (continuous_symm_of_isHomeomorph_mulEquiv Φ hΦ) hΦ.continuous Ψ hΨ
  map_add' := map_add _

theorem H2Transfer {G G' : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    {M M' : Type*} [AddCommGroup M] [DistribMulAction G M]
    [AddCommGroup M'] [DistribMulAction G' M']
    (Φ : G' ≃* G) (hΦ : IsHomeomorph (Φ : G' → G)) (Ψ : M' ≃+ M)
    (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m') :
    Nonempty (Work.AbsoluteKummer.H2 G' M' ≃+ Work.AbsoluteKummer.H2 G M) :=
  ⟨h2Transfer Φ hΦ Ψ hΨ⟩

end

end Work.SSGRoute.PT
