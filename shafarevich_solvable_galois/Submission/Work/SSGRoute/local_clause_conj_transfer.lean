import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open _root_.SSGRoute

open scoped Pointwise

/-!
# Transfer of the local clause along conjugation of a place

Let `A`, `B` be places of `ℚ̄` with `B = σ·A` (`x ∈ B ↔ ∃ y ∈ A, x = σ y`), for `σ ∈ G_ℚ`.
Then conjugation by `σ` is a group isomorphism `D_A ≃* D_B` of the decomposition groups, and a
local lift `l : D_A → Γ(τ+1)` of a homomorphism `ρ : G_ℚ → Γ(τ)` (with `LiftsFlowAt (l x) (ρ x)`
and `l x = 1` whenever `ρ x = 1`) transfers to a local lift

  `l' x = w · l (σ⁻¹ x σ) · w⁻¹`

of `D_B`, where `w ∈ Γ(τ+1)` is any lift of `ρ σ` (which exists because the projection
`Γ(τ+1) → Γ(τ)` is surjective).  Since `ρ (σ⁻¹ x σ) = (ρ σ)⁻¹ ρ x ρ σ`, the conjugated element
`w l(σ⁻¹ x σ) w⁻¹` lies over `ρ x`, and it is `1` whenever `ρ x = 1`.

This is the "local clause is conjugation-invariant" step of Theorem 15 (Schmidt–Wingberg).
-/

/-- If `B = σ·A`, then conjugation by `σ⁻¹` carries the decomposition group of `B` into the
decomposition group of `A`. -/
theorem mem_conj_decomp_of_mem (A B : ValuationSubring QBar) (σ : GalQ)
    (hAB : ∀ x : QBar, x ∈ B ↔ ∃ y : QBar, y ∈ A ∧ x = σ y) :
    ∀ x : GalQ, x ∈ decomp ℚ B → σ⁻¹ * x * σ ∈ decomp ℚ A := by
  have hB : B = σ • A := by
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := (hAB x).mp hx
      rw [hxy]
      show (σ⁻¹ : GalQ) • (σ • y) ∈ A
      rw [smul_smul, inv_mul_cancel, one_smul]
      exact hy
    · intro hx
      refine (hAB x).mpr ⟨(σ⁻¹ : GalQ) • x, hx, ?_⟩
      show x = (σ : GalQ) • ((σ⁻¹ : GalQ) • x)
      rw [smul_smul, mul_inv_cancel, one_smul]
  intro x hx
  have hA : σ⁻¹ • B = A := by rw [hB, smul_smul, inv_mul_cancel, one_smul]
  have hd := decomp_conj (k := ℚ) B σ⁻¹
  rw [hA] at hd
  rw [hd]
  refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
  show MulAut.conj σ⁻¹ x = σ⁻¹ * x * σ
  rw [MulAut.conj_apply, inv_inv]

/-- If `B = σ·A`, then conjugation by `σ` carries the decomposition group of `A` into the
decomposition group of `B`. -/
theorem mem_conj_decomp_of_mem' (A B : ValuationSubring QBar) (σ : GalQ)
    (hAB : ∀ x : QBar, x ∈ B ↔ ∃ y : QBar, y ∈ A ∧ x = σ y) :
    ∀ x : GalQ, x ∈ decomp ℚ A → σ * x * σ⁻¹ ∈ decomp ℚ B := by
  have hB : B = σ • A := by
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := (hAB x).mp hx
      rw [hxy]
      show (σ⁻¹ : GalQ) • (σ • y) ∈ A
      rw [smul_smul, inv_mul_cancel, one_smul]
      exact hy
    · intro hx
      refine (hAB x).mpr ⟨(σ⁻¹ : GalQ) • x, hx, ?_⟩
      show x = (σ : GalQ) • ((σ⁻¹ : GalQ) • x)
      rw [smul_smul, mul_inv_cancel, one_smul]
  intro x hx
  have hd := decomp_conj (k := ℚ) A σ
  rw [← hB] at hd
  rw [hd]
  refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
  show MulAut.conj σ x = σ * x * σ⁻¹
  rw [MulAut.conj_apply]

/-- Conjugation by `σ⁻¹` as a group homomorphism `D_B →* D_A`, for `B = σ·A`. -/
noncomputable def conjDecompHom (A B : ValuationSubring QBar) (σ : GalQ)
    (hAB : ∀ x : QBar, x ∈ B ↔ ∃ y : QBar, y ∈ A ∧ x = σ y) :
    ↥(decomp ℚ B) →* ↥(decomp ℚ A) where
  toFun x := ⟨σ⁻¹ * (x : GalQ) * σ, mem_conj_decomp_of_mem A B σ hAB x x.2⟩
  map_one' := by ext; simp
  map_mul' := by
    intro x y
    ext
    simp only [Subgroup.coe_mul]
    group

@[simp] theorem conjDecompHom_apply_coe (A B : ValuationSubring QBar) (σ : GalQ)
    (hAB : ∀ x : QBar, x ∈ B ↔ ∃ y : QBar, y ∈ A ∧ x = σ y) (x : ↥(decomp ℚ B)) :
    ((conjDecompHom A B σ hAB x : ↥(decomp ℚ A)) : GalQ) = σ⁻¹ * (x : GalQ) * σ := rfl

theorem local_clause_conj_transfer (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j n : ℕ)
    (ρ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (A B : ValuationSubring SSGRoute.QBar) (σ : SSGRoute.GalQ)
    (hAB : ∀ x : SSGRoute.QBar, x ∈ B ↔ ∃ y : SSGRoute.QBar, y ∈ A ∧ x = σ y)
    (h : ∃ l : ↥(SSGRoute.decomp ℚ A) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
          (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
        (∀ x : ↥(SSGRoute.decomp ℚ A), SSGRoute.LiftsFlowAt (l x) (ρ x)) ∧
        (∀ x : ↥(SSGRoute.decomp ℚ A), ρ x = 1 → l x = 1)) :
    ∃ l : ↥(SSGRoute.decomp ℚ B) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
          (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
      (∀ x : ↥(SSGRoute.decomp ℚ B), SSGRoute.LiftsFlowAt (l x) (ρ x)) ∧
      (∀ x : ↥(SSGRoute.decomp ℚ B), ρ x = 1 → l x = 1) := by
  obtain ⟨l, hl1, hl2⟩ := h
  obtain ⟨w, hw⟩ : ∃ w : Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
        (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
      flowGroupSucc p (K ≃ₐ[ℚ] K) n i j w = ρ σ :=
    ⟨flowGroupSection p (K ≃ₐ[ℚ] K) n i j (ρ σ),
      flowGroupSucc_section p (K ≃ₐ[ℚ] K) n i j (ρ σ)⟩
  have hpsi : ∀ x : ↥(decomp ℚ B), ρ (conjDecompHom A B σ hAB x) = (ρ σ)⁻¹ * ρ x * ρ σ := by
    intro x
    rw [conjDecompHom_apply_coe, map_mul, map_mul, map_inv]
  refine ⟨(MulAut.conj w).toMonoidHom.comp (l.comp (conjDecompHom A B σ hAB)), ?_, ?_⟩
  · intro x
    rw [liftsFlowAt_iff_flowGroupSucc]
    show flowGroupSucc p (K ≃ₐ[ℚ] K) n i j
      (MulAut.conj w (l (conjDecompHom A B σ hAB x))) = ρ x
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hw,
      (liftsFlowAt_iff_flowGroupSucc p K n i j _ _).mp (hl1 (conjDecompHom A B σ hAB x)),
      hpsi x]
    group
  · intro x hx
    show MulAut.conj w (l (conjDecompHom A B σ hAB x)) = 1
    rw [MulAut.conj_apply, hl2 (conjDecompHom A B σ hAB x) (by rw [hpsi x, hx]; group)]
    simp

end Work.SSGRoute
