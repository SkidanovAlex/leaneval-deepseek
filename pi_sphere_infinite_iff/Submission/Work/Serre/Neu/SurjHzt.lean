-- PORTED COPY (neutral island) of `Submission/Work/Serre/Surj/Hzt.lean`.
-- The only changes are: the imports of ratShuffle-island modules are redirected to the
-- copies in `Submission/Work/Serre/Neu/`, and the abbrev `singSSet` is renamed to
-- `singSSetN` (same body) so that this module can coexist with `Work.Serre.E0Defs`,
-- which declares the same name.  Declarations and proofs are unchanged.
import Submission.Work.Serre.Neu.SurjSetup2

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace Work.Serre.Surj

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

open Work.Cohomology

/-- **The generating cycle has a non-zero rational class.** -/
theorem tmul_one_homologyπ_ne_zero_of_hgen (P : Type) [TopologicalSpace P] (Q : Set P) (r : ℕ)
    (hgen : Nonempty ((relComplex ℚ (TopCat.of P) Q).homology (r + 1) ≅ ModuleCat.of ℚ ℚ))
    (z : ↥((relChains (TopCat.of P) Q).cycles (r + 1)))
    (hgenZ : ∀ w : ↥((relChains (TopCat.of P) Q).homology (r + 1)),
      ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ,
        TensorProduct.tmul ℤ (n • w) (1 : ℚ)
          = TensorProduct.tmul ℤ (m • ((ModuleCat.Hom.hom
              ((relChains (TopCat.of P) Q).homologyπ (r + 1))) z)) (1 : ℚ)) :
    TensorProduct.tmul ℤ ((ModuleCat.Hom.hom
        ((relChains (TopCat.of P) Q).homologyπ (r + 1))) z) (1 : ℚ) ≠ 0 := by
  intro h0
  obtain ⟨eC⟩ := hgen
  set H : Type := ↥((relChains (TopCat.of P) Q).homology (r + 1)) with hH
  set x : H := (ModuleCat.Hom.hom ((relChains (TopCat.of P) Q).homologyπ (r + 1))) z with hx
  -- the pure tensor `1 ⊗ [z]` vanishes in `ℚ ⊗[ℤ] H`
  have hz0 : TensorProduct.tmul ℤ (1 : ℚ) x = 0 := by
    have hc := congrArg (TensorProduct.comm ℤ H ℚ) h0
    rw [map_zero, TensorProduct.comm_tmul] at hc
    exact hc
  -- every `ℤ`-linear functional on `H` vanishes
  have hfun : ∀ g : H →ₗ[ℤ] ℚ, g = 0 := by
    intro g
    let ev : TensorProduct ℤ ℚ H →ₗ[ℤ] ℚ :=
      TensorProduct.lift (LinearMap.mk₂ ℤ (fun q w => q * g w)
        (fun a b w => by rw [add_mul])
        (fun c a w => by
          rw [← Int.cast_smul_eq_zsmul ℚ c a, smul_eq_mul,
            ← Int.cast_smul_eq_zsmul ℚ c (a * g w), smul_eq_mul, mul_assoc])
        (fun q a b => by rw [map_add, mul_add])
        (fun c q w => by
          rw [LinearMap.map_smul, ← Int.cast_smul_eq_zsmul ℚ c (g w), smul_eq_mul,
            ← Int.cast_smul_eq_zsmul ℚ c (q * g w), smul_eq_mul]; ring))
    have hev : ∀ (q : ℚ) (w : H), ev (TensorProduct.tmul ℤ q w) = q * g w := fun q w => rfl
    ext w
    obtain ⟨n, hn, m, hm⟩ := hgenZ w
    have hmn : TensorProduct.tmul ℤ (1 : ℚ) (n • w)
        = TensorProduct.tmul ℤ (1 : ℚ) (m • x) := by
      have hc := congrArg (TensorProduct.comm ℤ H ℚ) hm
      rw [TensorProduct.comm_tmul, TensorProduct.comm_tmul, hx] at hc
      exact hc
    have hnm : n • (TensorProduct.tmul ℤ (1 : ℚ) w) = 0 := by
      rw [TensorProduct.tmul_smul (R := ℤ) (R' := ℕ) n (1 : ℚ) w] at hmn
      rcases Int.eq_nat_or_neg m with ⟨k, hk | hk⟩
      · rw [hk, natCast_zsmul,
          TensorProduct.tmul_smul (R := ℤ) (R' := ℕ) k (1 : ℚ) x, hz0, smul_zero] at hmn
        exact hmn
      · rw [hk, neg_zsmul, natCast_zsmul, TensorProduct.tmul_neg,
          TensorProduct.tmul_smul (R := ℤ) (R' := ℕ) k (1 : ℚ) x, hz0,
          smul_zero, neg_zero] at hmn
        exact hmn
    have h1 : n • g w = 0 := by
      have h2 := congrArg ev hnm
      rw [map_zero, map_nsmul, hev (1 : ℚ) w, one_mul] at h2
      exact h2
    rw [LinearMap.zero_apply]
    have h3 : (n : ℚ) * g w = 0 := by
      rw [nsmul_eq_mul] at h1
      exact_mod_cast h1
    exact (mul_eq_zero.mp h3).resolve_left (by exact_mod_cast hn.ne')
  haveI hsub : Subsingleton (H →ₗ[ℤ] ℚ) :=
    subsingleton_iff.mpr (fun g g' => by rw [hfun g, hfun g'])
  -- hence the relative cohomology in degree `r+1` is trivial, contradicting `hgen`
  obtain ⟨eD⟩ := Work.Serre.relCohRat_dual P Q (r + 1)
  have hsub2 : Subsingleton (↥(Work.Thom.RelCoh ℚ (r + 1) P Q)) :=
    Function.Surjective.subsingleton ((ModuleCat.epi_iff_surjective eD.inv).mp inferInstance)
  have hsub3 : Subsingleton ℚ :=
    Function.Surjective.subsingleton ((ModuleCat.epi_iff_surjective eC.hom).mp inferInstance)
  exact one_ne_zero (Subsingleton.elim (1 : ℚ) 0)

end

end Work.Serre.Surj
