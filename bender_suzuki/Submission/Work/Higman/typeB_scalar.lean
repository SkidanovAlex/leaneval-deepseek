import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.typeB
import Submission.Work.Higman.card_eq_sq_or_cube
import Submission.Work.Higman.BS.Defs
import Submission.Work.Higman.BS.fpf
import Submission.Work.Higman.mulAut_norm_im
import Submission.Work.Higman.card_isXiLayer_eq
import Submission.Work.Higman.BS.quot_elementary
import Submission.Work.Higman.scalar_module_of_layers

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

set_option maxHeartbeats 1000000

/-! ## Glue between `V` as a (commutative) group and as an `𝔽₂`-vector space -/

section Glue

variable {V : Type} [CommGroup V]

/-- Membership in `Subgroup.toAddSubgroup`. -/
theorem mem_toAddSubgroup_iff (S : Subgroup V) (x : Additive V) :
    x ∈ Subgroup.toAddSubgroup S ↔ Additive.toMul x ∈ S := by
  show x ∈ (Subgroup.toAddSubgroup S : Set _) ↔ Additive.toMul x ∈ (S : Set V)
  rw [show ((Subgroup.toAddSubgroup S : AddSubgroup (Additive V)) : Set (Additive V)) =
      (S : Set V) from rfl]
  rfl

/-- Cardinality of `Subgroup.toAddSubgroup`. -/
theorem card_toAddSubgroup (S : Subgroup V) :
    Nat.card ↥(Subgroup.toAddSubgroup S) = Nat.card ↥S := by
  refine Nat.card_congr
    { toFun := fun x => ⟨Additive.toMul x.1, (mem_toAddSubgroup_iff S x.1).mp x.2⟩
      invFun := fun x => ⟨Additive.ofMul x.1,
        (mem_toAddSubgroup_iff S (Additive.ofMul x.1)).mpr (by simpa using x.2)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }

end Glue

/-! ## The translated hypotheses -/

section Setup

variable {P : Type} [Group P] [Finite P]

/-- The `φ`-invariant subgroups of a finite group of order `q`. -/
abbrev InvSubgroupsMul (V : Type) [Group V] (q : ℕ) (φ : MulAut V) : Type _ :=
  {N : Subgroup V // (∀ v ∈ N, φ v ∈ N) ∧ Nat.card N = q}

/-- The `σ`-invariant additive subgroups of a finite additive group of order `q`. -/
abbrev InvSubgroups (V : Type) [AddCommGroup V] (q : ℕ) (σ : V → V) : Type _ :=
  {M : AddSubgroup V // (∀ x ∈ M, σ x ∈ M) ∧ Nat.card M = q}

/-- The number of `ξ`-layers is the number of `σ`-invariant subgroups of `P ⧸ Z(P)` of order
`|Z(P)|`; this is the translated form of `IsTypeB`. -/
theorem layer_count_quot (h : IsSuzuki2Grp P) (ξ : MulAut P) (hB : IsTypeB ξ) :
    Nat.card ↥(Subgroup.center P) + 1 ≤
      Nat.card (InvSubgroupsMul (P ⧸ Subgroup.center P)
        (Nat.card ↥(Subgroup.center P)) (quotCenterAut ξ)) := by
  rw [← card_isXiLayer_eq h ξ]
  exact hB

/-- `ξ ^ k` has no non-trivial fixed point on `P ⧸ Z(P)`. -/
theorem quotCenterAut_fpf (h : IsSuzuki2Grp P) {ξ : MulAut P} (hξ : FpfXi ξ) :
    ∀ k : ℕ, ξ ^ k ≠ 1 → ∀ v : P ⧸ Subgroup.center P,
      ((quotCenterAut ξ) ^ k) v = v → v = 1 := by
  intro k hk v hv
  obtain ⟨x, rfl⟩ := centerProj_surjective v
  have h2 : QuotientGroup.mk' (Subgroup.center P) ((ξ ^ k) x) =
      QuotientGroup.mk' (Subgroup.center P) x := by
    rw [← quotCenterAut_pow_mk ξ k x]
    exact hv
  have h3 : ((ξ ^ k) x)⁻¹ * x ∈ Subgroup.center P := QuotientGroup.eq.mp h2
  have h4 : x⁻¹ * (ξ ^ k) x ∈ Subgroup.center P := by
    simpa [mul_inv_rev] using (Subgroup.center P).inv_mem h3
  have h5 : x ∈ Subgroup.center P := mem_center_of_mul_mem_center h hξ hk h4
  show QuotientGroup.mk' (Subgroup.center P) x = 1
  exact (QuotientGroup.eq_one_iff x).mpr h5

end Setup

/-! ## The main theorem -/

/-- **D2 (scalar form of type `B`).**  If `P` is of type `B`, then `P / Z(P)` carries the
structure of a 2-dimensional `𝔽_q`-space on which `ξ` acts as a scalar — equivalently there are a
field `F` of order `q = |Z(P)|` and a surjective additive `ψ : P → F × F` with kernel `Z(P)`
through which `ξ` is a scalar. -/
theorem typeB_scalar {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {ξ : MulAut P} (hξ : Work.Higman.FpfXi ξ)
    (hB : Work.Higman.IsTypeB ξ) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (ψ : P → F × F),
      Nat.card F = Nat.card ↥(Subgroup.center P) ∧
      (∀ x y, ψ (x * y) = ψ x + ψ y) ∧ (∀ x, ψ x = 0 ↔ x ∈ Subgroup.center P) ∧
      Function.Surjective ψ ∧ ∃ lam : Fˣ, ∀ x, ψ (ξ x) = (lam : F) • ψ x := by
  classical
  -- ## Step 1: the translated type-`B` hypothesis and fixed-point-freeness
  have hN : Nat.card ↥(Subgroup.center P) + 1 ≤
      Nat.card (InvSubgroupsMul (P ⧸ Subgroup.center P)
        (Nat.card ↥(Subgroup.center P)) (quotCenterAut ξ)) :=
    layer_count_quot h ξ hB
  have hfpf : ∀ k : ℕ, ξ ^ k ≠ 1 → ∀ v : P ⧸ Subgroup.center P,
      ((quotCenterAut ξ) ^ k) v = v → v = 1 := quotCenterAut_fpf h hξ
  -- ## Step 2: `P ⧸ Z(P)` is elementary abelian, hence an `𝔽₂`-vector space
  have hsq : ∀ v : P ⧸ Subgroup.center P, v ^ 2 = 1 :=
    quotCenter_isElementary_aux h hξ hfpf hN
  have hcomm : ∀ v w : P ⧸ Subgroup.center P, v * w = w * v := by
    intro v w
    have hv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq v)
    have hw : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq w)
    have hvw : (v * w)⁻¹ = v * w :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq (v * w))
    rw [← hvw, mul_inv_rev, hv, hw]
  letI : CommGroup (P ⧸ Subgroup.center P) :=
    { (inferInstance : Group (P ⧸ Subgroup.center P)) with mul_comm := hcomm }
  have h2smul : ∀ x : Additive (P ⧸ Subgroup.center P), (2 : ℕ) • x = 0 := by
    intro x
    obtain ⟨v, rfl⟩ : ∃ v, Additive.ofMul v = x := ⟨Additive.toMul x, by simp⟩
    rw [show (2 : ℕ) • Additive.ofMul v = Additive.ofMul (v ^ 2) from by simp, hsq v]
    rfl
  letI : Module (ZMod 2) (Additive (P ⧸ Subgroup.center P)) :=
    AddCommGroup.zmodModule h2smul
  -- ## Step 3: the induced linear automorphism `σ`
  let σ : Additive (P ⧸ Subgroup.center P) →ₗ[ZMod 2] Additive (P ⧸ Subgroup.center P) :=
    { toFun := fun x => (MulEquiv.toAdditive (quotCenterAut ξ)) x
      map_add' := fun x y => (MulEquiv.toAdditive (quotCenterAut ξ)).map_add x y
      map_smul' := by
        intro c x
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with rfl | rfl <;>
          simp only [RingHom.id_apply, zero_smul, one_smul, map_zero] }
  have hσact : ∀ (i : ℕ) (v : P ⧸ Subgroup.center P),
      (σ ^ i) (Additive.ofMul v) = Additive.ofMul (((quotCenterAut ξ) ^ i) v) := by
    intro i
    induction i with
    | zero => intro v; simp
    | succ i ih =>
        intro v
        have hstep : σ (Additive.ofMul v) = Additive.ofMul ((quotCenterAut ξ) v) := rfl
        rw [pow_succ, Module.End.mul_apply, hstep, ih, pow_succ, MulAut.mul_apply]
  have hσpow_eq : ∀ i : ℕ, σ ^ i = 1 ↔ (quotCenterAut ξ) ^ i = 1 := by
    intro i
    constructor
    · intro h1
      ext v
      have h3 := congrArg (fun f => f (Additive.ofMul v)) h1
      rw [hσact, Module.End.one_apply] at h3
      simpa using h3
    · intro h1
      ext x
      obtain ⟨v, rfl⟩ : ∃ v, Additive.ofMul v = x := ⟨Additive.toMul x, by simp⟩
      rw [hσact, h1]
      simp
  -- ## Step 4: the hypotheses of the module dichotomy
  have hqc : orderOf (quotCenterAut ξ) = orderOf ξ := by
    refine Nat.dvd_antisymm ?_ ?_
    · rw [orderOf_dvd_iff_pow_eq_one, quotCenterAut_pow_eq_one_iff h hξ]
      exact pow_orderOf_eq_one ξ
    · rw [orderOf_dvd_iff_pow_eq_one, ← quotCenterAut_pow_eq_one_iff h hξ]
      exact pow_orderOf_eq_one _
  have hordσ : orderOf σ = Nat.card ↥(Subgroup.center P) - 1 := by
    have h1 : orderOf σ = orderOf (quotCenterAut ξ) := by
      refine Nat.dvd_antisymm ?_ ?_
      · rw [orderOf_dvd_iff_pow_eq_one, hσpow_eq]
        exact pow_orderOf_eq_one _
      · rw [orderOf_dvd_iff_pow_eq_one, ← hσpow_eq]
        exact pow_orderOf_eq_one _
    rw [h1, hqc, hξ.order]
  have hcardV : Nat.card (Additive (P ⧸ Subgroup.center P)) =
      Nat.card ↥(Subgroup.center P) ^ 2 := by
    have hcard_quot : Nat.card (P ⧸ Subgroup.center P) * Nat.card ↥(Subgroup.center P) =
        Nat.card P := by
      rw [← Subgroup.index_eq_card, Subgroup.index_mul_card]
    have hcardP : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 3 := hξ.card_cube
    have hpos : 0 < Nat.card ↥(Subgroup.center P) := Nat.card_pos
    have hV : Nat.card (P ⧸ Subgroup.center P) = Nat.card ↥(Subgroup.center P) ^ 2 := by
      have h3 : Nat.card (P ⧸ Subgroup.center P) * Nat.card ↥(Subgroup.center P) =
          Nat.card ↥(Subgroup.center P) ^ 2 * Nat.card ↥(Subgroup.center P) := by
        rw [hcard_quot, hcardP]; ring
      exact Nat.eq_of_mul_eq_mul_right hpos h3
    rw [Nat.card_congr (Additive.toMul (α := P ⧸ Subgroup.center P)), hV]
  have hq2 : 2 ≤ Nat.card ↥(Subgroup.center P) := by
    have h4 : 4 ≤ Nat.card (omega1 P) := h.omega1_card_ge_four
    have h5 : Nat.card (omega1 P) ≤ Nat.card ↥(Subgroup.center P) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion (h.omega1_le_center))
        (Subgroup.inclusion_injective _)
    omega
  have hfpfσ : ∀ k : ℕ, σ ^ k ≠ 1 → ∀ x : Additive (P ⧸ Subgroup.center P),
      (σ ^ k) x = x → x = 0 := by
    intro k hk x hx
    obtain ⟨v, rfl⟩ : ∃ v, Additive.ofMul v = x := ⟨Additive.toMul x, by simp⟩
    rw [hσact] at hx
    have h1 : ((quotCenterAut ξ) ^ k) v = v := Additive.ofMul.injective hx
    have hk' : ξ ^ k ≠ 1 := fun hcon => hk ((hσpow_eq k).mpr
      ((quotCenterAut_pow_eq_one_iff h hξ k).mpr hcon))
    rw [hfpf k hk' v h1]
    rfl
  have hNσ : Nat.card ↥(Subgroup.center P) + 1 ≤
      Nat.card (InvSubgroups (Additive (P ⧸ Subgroup.center P))
        (Nat.card ↥(Subgroup.center P)) σ) := by
    have hmaps : ∀ N : InvSubgroupsMul (P ⧸ Subgroup.center P)
        (Nat.card ↥(Subgroup.center P)) (quotCenterAut ξ),
        (∀ x ∈ Subgroup.toAddSubgroup N.1, σ x ∈ Subgroup.toAddSubgroup N.1) ∧
          Nat.card ↥(Subgroup.toAddSubgroup N.1) = Nat.card ↥(Subgroup.center P) := by
      intro N
      constructor
      · intro x hx
        rw [mem_toAddSubgroup_iff] at hx ⊢
        rw [show σ x = Additive.ofMul (quotCenterAut ξ (Additive.toMul x)) from rfl]
        exact N.2.1 _ hx
      · rw [card_toAddSubgroup]
        exact N.2.2
    refine le_trans hN (Nat.card_le_card_of_injective
      (fun N : InvSubgroupsMul (P ⧸ Subgroup.center P)
          (Nat.card ↥(Subgroup.center P)) (quotCenterAut ξ) =>
        (⟨Subgroup.toAddSubgroup N.1, hmaps N⟩ : InvSubgroups (Additive (P ⧸ Subgroup.center P))
          (Nat.card ↥(Subgroup.center P)) σ)) ?_)
    intro N₁ N₂ h
    exact Subtype.ext (Subgroup.toAddSubgroup.injective (congrArg Subtype.val h))
  -- ## Step 5: apply the module dichotomy
  obtain ⟨F, hF, hFint, ψV, lam, hcardF, hadd, heq⟩ :=
    scalar_module_of_layers σ (Nat.card ↥(Subgroup.center P)) hq2 hcardV hordσ hfpfσ hNσ
  have hψ0 : ψV 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    have h2 : ψV 0 + 0 = ψV 0 + ψV 0 := by rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  -- ## Step 6: assemble
  refine ⟨F, hF, hFint, fun x => ψV (Additive.ofMul (centerProj x)), hcardF, ?_, ?_, ?_, lam, ?_⟩
  · -- additivity
    intro x y
    show ψV (Additive.ofMul (centerProj (x * y))) =
      ψV (Additive.ofMul (centerProj x)) + ψV (Additive.ofMul (centerProj y))
    rw [map_mul, show Additive.ofMul (centerProj x * centerProj y) =
      Additive.ofMul (centerProj x) + Additive.ofMul (centerProj y) from by simp]
    exact hadd _ _
  · -- kernel
    intro x
    constructor
    · intro hx
      have hx' : ψV (Additive.ofMul (centerProj x)) = 0 := hx
      have h1 : Additive.ofMul (centerProj x) = 0 := by
        apply ψV.injective
        show ψV (Additive.ofMul (centerProj x)) = ψV 0
        rw [hx', hψ0]
      have h2 : centerProj x = 1 := Additive.ofMul.injective (by simpa using h1)
      exact (QuotientGroup.eq_one_iff x).mp h2
    · intro hx
      have h1 : centerProj x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      show ψV (Additive.ofMul (centerProj x)) = 0
      rw [h1]
      simpa using hψ0
  · -- surjectivity
    intro y
    obtain ⟨z, hz⟩ := ψV.surjective y
    obtain ⟨w, rfl⟩ : ∃ w, Additive.ofMul w = z := ⟨Additive.toMul z, by simp⟩
    obtain ⟨x, rfl⟩ := centerProj_surjective w
    exact ⟨x, hz⟩
  · -- equivariance
    intro x
    have h1 : (MulEquiv.toAdditive (quotCenterAut ξ)) (Additive.ofMul (centerProj x)) =
        Additive.ofMul (centerProj (ξ x)) := by
      rw [← quotCenterAut_mk]
      rfl
    show ψV (Additive.ofMul (centerProj (ξ x))) = (lam : F) • ψV (Additive.ofMul (centerProj x))
    rw [← h1]
    exact heq _

end Work.Higman
