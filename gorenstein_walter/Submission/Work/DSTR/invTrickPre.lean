import Mathlib
import Submission.Work.DSTR.invTrickAbelian
import Submission.OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03
import Submission.OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroupsCoprime

/-!
# `Work.DSTR.invTrickPre` — tools for the inversion trick

Restriction of an automorphism to a characteristic subgroup, and the
automorphism induced on a quotient by an invariant normal subgroup, together with
the elementary facts used by `Work.DSTR.invTrickSolvable`.
-/

namespace Work.DSTR

open Subgroup

/-! ## Restriction to a characteristic subgroup -/

/-- Restriction of an automorphism of `G` to a characteristic subgroup `H ≤ G`. -/
noncomputable def invTrickRestrict {G : Type*} [Group G] (H : Subgroup G) [H.Characteristic]
    (ρ : MulAut G) : MulAut ↥H where
  toFun x := ⟨ρ x, by
    have h : Subgroup.map ρ.toMonoidHom H = H :=
      (Subgroup.characteristic_iff_map_eq.mp inferInstance) ρ
    exact (Subgroup.map_le_iff_le_comap.mp (le_of_eq h)) x.2⟩
  invFun x := ⟨ρ⁻¹ x, by
    have h : Subgroup.map (ρ⁻¹).toMonoidHom H = H :=
      (Subgroup.characteristic_iff_map_eq.mp inferInstance) ρ⁻¹
    exact (Subgroup.map_le_iff_le_comap.mp (le_of_eq h)) x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by
    show ρ ((x : G) * (y : G)) = ρ (x : G) * ρ (y : G)
    rw [map_mul])

/-- The monoid homomorphism `MulAut G →* MulAut ↥H` given by restriction to a characteristic
subgroup. -/
noncomputable def invTrickRestrictHom {G : Type*} [Group G] (H : Subgroup G) [H.Characteristic] :
    MulAut G →* MulAut ↥H where
  toFun ρ := invTrickRestrict H ρ
  map_one' := by
    apply MulEquiv.ext; intro x; apply Subtype.ext; simp [invTrickRestrict]
  map_mul' ρ σ := by
    apply MulEquiv.ext; intro x; apply Subtype.ext
    simp [invTrickRestrict, MulAut.mul_apply]

@[simp] theorem invTrickRestrictHom_apply_coe {G : Type*} [Group G] (H : Subgroup G)
    [H.Characteristic] (ρ : MulAut G) (x : H) :
    ((invTrickRestrictHom H ρ) x : G) = ρ x := rfl

theorem orderOf_invTrickRestrictHom_dvd {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    [H.Characteristic] (ρ : MulAut G) :
    orderOf (invTrickRestrictHom H ρ) ∣ orderOf ρ :=
  orderOf_map_dvd (invTrickRestrictHom H) ρ

/-! ## The induced automorphism of a quotient -/

/-- The automorphism of `G ⧸ N` induced by an automorphism `ρ` of `G` which preserves the
normal subgroup `N`. -/
noncomputable def invTrickQuotMulAut {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (ρ : MulAut G) (hρ : Subgroup.map (ρ : G ≃* G) N = N) : MulAut (G ⧸ N) :=
  QuotientGroup.congr N N ρ hρ

theorem invTrickQuotMulAut_apply {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (ρ : MulAut G) (hρ : Subgroup.map (ρ : G ≃* G) N = N) (x : G) :
    invTrickQuotMulAut N ρ hρ (QuotientGroup.mk' N x) = QuotientGroup.mk' N (ρ x) :=
  QuotientGroup.congr_apply N N ρ hρ x

theorem invTrickQuotMulAut_inv_apply {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (ρ : MulAut G) (hρ : Subgroup.map (ρ : G ≃* G) N = N) (x : G) :
    (invTrickQuotMulAut N ρ hρ)⁻¹ (QuotientGroup.mk' N x) = QuotientGroup.mk' N (ρ⁻¹ x) := by
  have h : invTrickQuotMulAut N ρ hρ (QuotientGroup.mk' N (ρ⁻¹ x))
      = QuotientGroup.mk' N x := by
    rw [invTrickQuotMulAut_apply]
    simp
  rw [← h, MulAut.inv_apply_self]

theorem invTrickQuotMulAut_pow_apply {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (ρ : MulAut G) (hρ : Subgroup.map (ρ : G ≃* G) N = N) (n : ℕ) (x : G) :
    (invTrickQuotMulAut N ρ hρ ^ n) (QuotientGroup.mk' N x)
      = QuotientGroup.mk' N ((ρ ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, invTrickQuotMulAut_apply, pow_succ', MulAut.mul_apply]

/-- Membership in `N` read off from equality of cosets: `x N = y N ↔ x * y⁻¹ ∈ N`. -/
theorem invTrickQuot_eq_iff {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {x y : G} :
    QuotientGroup.mk' N x = QuotientGroup.mk' N y ↔ x * y⁻¹ ∈ N := by
  constructor
  · intro h
    rw [QuotientGroup.mk'_eq_mk'] at h
    obtain ⟨z, hz, hzy⟩ := h
    have hxy : x⁻¹ * y ∈ N := by
      have hzx : x⁻¹ * y = z := by rw [← hzy]; group
      rwa [hzx]
    have hm : (x⁻¹ * y)⁻¹ ∈ N := N.inv_mem hxy
    have heq : x * y⁻¹ = x * (x⁻¹ * y)⁻¹ * x⁻¹ := by group
    rw [heq]
    exact (inferInstance : N.Normal).conj_mem _ hm x
  · intro h
    rw [QuotientGroup.mk'_eq_mk']
    refine ⟨x⁻¹ * y, ?_, by group⟩
    have hm : (x * y⁻¹)⁻¹ ∈ N := N.inv_mem h
    have heq : x⁻¹ * y = x⁻¹ * (x * y⁻¹)⁻¹ * (x⁻¹)⁻¹ := by group
    rw [heq]
    exact (inferInstance : N.Normal).conj_mem _ hm x⁻¹

/-! ## The abelian case of the inversion trick on a quotient -/

/-- `quotient` version of the abelian case of the inversion trick used in
`invTrickSolvable`: applied to an abelian group which arises as a quotient. -/
theorem invTrickAbelianQuot {F : Type*} [Group F] [Finite F] {N : Subgroup F} [N.Normal]
    (hab : commutator F ≤ N) (hNodd : Odd (Nat.card (F ⧸ N)))
    {τ ξ : MulAut F} (hτN : Subgroup.map (τ : F ≃* F) N = N)
    (hξN : Subgroup.map (ξ : F ≃* F) N = N)
    (hτ2 : τ * τ = 1)
    (hcop : Nat.Coprime (orderOf ξ) (Nat.card F)) (hξodd : Odd (orderOf ξ))
    (hconj : τ * ξ * τ⁻¹ = ξ⁻¹)
    (hfix : ∀ q : F ⧸ N, invTrickQuotMulAut N τ hτN q = q →
      invTrickQuotMulAut N ξ hξN q = q) : invTrickQuotMulAut N ξ hξN = 1 := by
  haveI hcomm : IsMulCommutative (F ⧸ N) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hab
  letI : CommGroup (F ⧸ N) :=
    { (inferInstance : Group (F ⧸ N)) with mul_comm := fun a b => mul_comm' a b }
  have hτ2' : invTrickQuotMulAut N τ hτN * invTrickQuotMulAut N τ hτN = 1 := by
    apply MulEquiv.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [MulAut.mul_apply, invTrickQuotMulAut_apply, invTrickQuotMulAut_apply]
    have h2 : τ (τ x) = x := by
      have h := congrArg (fun f : MulAut F => f x) hτ2
      simpa [MulAut.mul_apply] using h
    rw [h2]
    rfl
  have hconj' : invTrickQuotMulAut N τ hτN * invTrickQuotMulAut N ξ hξN
      * (invTrickQuotMulAut N τ hτN)⁻¹ = (invTrickQuotMulAut N ξ hξN)⁻¹ := by
    apply MulEquiv.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [MulAut.mul_apply, MulAut.mul_apply, invTrickQuotMulAut_inv_apply,
      invTrickQuotMulAut_apply, invTrickQuotMulAut_apply, invTrickQuotMulAut_inv_apply]
    have h := congrArg (fun f : MulAut F => f x) hconj
    simp only [MulAut.mul_apply] at h
    rw [h]
  have hcop' : Nat.Coprime (orderOf (invTrickQuotMulAut N ξ hξN)) (Nat.card (F ⧸ N)) := by
    refine Nat.Coprime.coprime_dvd_left ?_ (hcop.coprime_dvd_right
      ⟨Nat.card ↥N, Subgroup.card_eq_card_quotient_mul_card_subgroup N⟩)
    refine (orderOf_dvd_iff_pow_eq_one).mpr ?_
    apply MulEquiv.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [invTrickQuotMulAut_pow_apply, pow_orderOf_eq_one]
    simp
  have hξodd' : Odd (orderOf (invTrickQuotMulAut N ξ hξN)) :=
    Odd.of_dvd_nat hξodd (by
      refine (orderOf_dvd_iff_pow_eq_one).mpr ?_
      apply MulEquiv.ext
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
      rw [invTrickQuotMulAut_pow_apply, pow_orderOf_eq_one]
      simp)
  exact invTrickAbelian hNodd hτ2' hcop' hξodd' hconj' hfix

end Work.DSTR
