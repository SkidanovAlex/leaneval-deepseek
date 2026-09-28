import Mathlib
import Submission.Work.Q44Geom.Setup
import Submission.Work.Q44Geom.invSub_finrank_le

/-!
# The invariance subspace of a cubic form without a linear factor has dimension `≤ 3`

`Work.Q44Geom.invSub B` is the space of directions `w` with `B(x + t w) = B(x)` for all `x, t`.
For a nonzero homogeneous cubic `B` in `5` variables with no linear factor we show
`finrank ℚ (invSub B) ≤ 3`.

The proof linearises the defining property: if `w ∈ invSub B` then the directional derivative
`Σ i, w i • ∂ᵢ B` vanishes (the coefficient of `t` in `B(x + t w)`), hence `invSub B ≤ ker Φ`
for `Φ w = Σ i, w i • ∂ᵢ B`.  Rank–nullity then forces `dim (invSub B) ≤ 3` unless the partial
derivatives span a space of dimension `≤ 1`.  In that case Euler's identity
`Σ i, X i • ∂ᵢ B = 3 • B` exhibits `B` as the product of a linear form and a quadratic form,
contradicting the absence of linear factors.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MvPolynomial

namespace Work.HP.MDEstimates

/-! ## Degenerate partial derivatives for a cubic force a linear factor -/

/-- If the partial derivatives of a nonzero homogeneous cubic `B` in `5` variables span a
space of dimension `≤ 1`, then `B` has a linear factor, whence `hnolin` gives a contradiction. -/
theorem false_of_cub_pderiv_span_finrank_le_one (B : MvPolynomial (Fin 5) ℚ)
    (hB : B.IsHomogeneous 3) (hB0 : B ≠ 0)
    (h : Module.finrank ℚ
      (Submodule.span ℚ (Set.range fun i : Fin 5 => MvPolynomial.pderiv i B)) ≤ 1)
    (hnolin : ∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ B → False) : False := by
  set V' : Submodule ℚ (MvPolynomial (Fin 5) ℚ) :=
    Submodule.span ℚ (Set.range fun i : Fin 5 => MvPolynomial.pderiv i B) with hV'_def
  haveI hfin : FiniteDimensional ℚ ↥V' :=
    Module.Finite.span_of_finite ℚ (Set.finite_range (fun i : Fin 5 => MvPolynomial.pderiv i B))
  have hsmall : Module.finrank ℚ V' ≤ 1 := by rw [hV'_def]; exact h
  by_cases hbot : V' = ⊥
  · exfalso
    have hall : ∀ i : Fin 5, MvPolynomial.pderiv i B = 0 := by
      intro i
      have hi : MvPolynomial.pderiv i B ∈ V' := Submodule.subset_span (Set.mem_range_self i)
      rw [hbot] at hi; simpa using hi
    have heuler := hB.sum_X_mul_pderiv
    rw [Finset.sum_eq_zero (fun i _ => by rw [hall i, mul_zero])] at heuler
    have h3 : (3 : ℚ) • B = 0 := (Nat.cast_smul_eq_nsmul ℚ 3 B).trans heuler.symm
    exact hB0 ((smul_eq_zero.mp h3).resolve_left (by norm_num))
  · have hex : ∃ i : Fin 5, MvPolynomial.pderiv i B ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hbot (by
        rw [hV'_def, Submodule.span_eq_bot]
        rintro _ ⟨i, rfl⟩
        exact hc i)
    obtain ⟨i₀, hi₀⟩ := hex
    have hV'_eq : V' = ℚ ∙ MvPolynomial.pderiv i₀ B := by
      have hle : ℚ ∙ MvPolynomial.pderiv i₀ B ≤ V' := by
        rw [Submodule.span_le]; rintro _ rfl; exact Submodule.subset_span (Set.mem_range_self i₀)
      have hfr : Module.finrank ℚ (ℚ ∙ MvPolynomial.pderiv i₀ B) = 1 :=
        finrank_span_singleton hi₀
      exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hfr]; exact hsmall)).symm
    have hc : ∀ i : Fin 5, ∃ cc : ℚ, cc • MvPolynomial.pderiv i₀ B = MvPolynomial.pderiv i B := by
      intro i
      have hi : MvPolynomial.pderiv i B ∈ V' := Submodule.subset_span (Set.mem_range_self i)
      rw [hV'_eq] at hi
      exact Submodule.mem_span_singleton.mp hi
    choose c hc' using hc
    have hL : (∑ i : Fin 5, c i • (MvPolynomial.X i : MvPolynomial (Fin 5) ℚ))
        * MvPolynomial.pderiv i₀ B = 3 • B := by
      rw [← hB.sum_X_mul_pderiv, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← hc' i, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
      ring
    have hB_eq : B = (∑ i : Fin 5, c i • (MvPolynomial.X i : MvPolynomial (Fin 5) ℚ))
        * (MvPolynomial.C (1/3 : ℚ) * MvPolynomial.pderiv i₀ B) := by
      have h3f : MvPolynomial.C (1/3 : ℚ) * ((3 : ℕ) • B) = B := by
        rw [show (3 : ℕ) • B = MvPolynomial.C ((3 : ℕ) : ℚ) * B from
          (Nat.cast_smul_eq_nsmul ℚ 3 B).symm.trans (MvPolynomial.smul_eq_C_mul B ((3 : ℕ) : ℚ))]
        rw [← mul_assoc, ← MvPolynomial.C_mul,
          show (1/3 : ℚ) * ((3 : ℕ) : ℚ) = 1 by norm_num, MvPolynomial.C_1, one_mul]
      have h6 := congrArg (fun z => MvPolynomial.C (1/3 : ℚ) * z) hL
      rw [h3f] at h6
      exact h6.symm.trans (by ring)
    have hL_hom : (∑ i : Fin 5, c i • (MvPolynomial.X i : MvPolynomial (Fin 5) ℚ)).IsHomogeneous 1 := by
      apply MvPolynomial.IsHomogeneous.sum
      intro i _
      rw [MvPolynomial.smul_eq_C_mul]
      simpa using (MvPolynomial.isHomogeneous_C (Fin 5) (c i)).mul
        (MvPolynomial.isHomogeneous_X ℚ i)
    by_cases hL0 : (∑ i : Fin 5, c i • (MvPolynomial.X i : MvPolynomial (Fin 5) ℚ)) = 0
    · exact hB0 (by rw [hB_eq, hL0, zero_mul])
    · exact hnolin _ hL_hom ⟨MvPolynomial.C (1/3 : ℚ) * MvPolynomial.pderiv i₀ B, hB_eq⟩

/-! ## The main theorem -/

theorem cubInv_finrank_le (B : MvPolynomial (Fin 5) ℚ) (hB : B.IsHomogeneous 3) (hB0 : B ≠ 0)
    (hnolin : ∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ B → False) :
    Module.finrank ℚ (Work.Q44Geom.invSub B) ≤ 3 := by
  have hker : Work.Q44Geom.invSub B ≤ (Work.Q44Geom.formPhi B).ker := by
    intro w hw
    rw [LinearMap.mem_ker, Work.Q44Geom.formPhi_apply]
    exact Work.Q44Geom.sum_smul_pderiv_eq_zero_of_mem_invSub B w hw
  have hspan_le : Submodule.span ℚ (Set.range fun i : Fin 5 => MvPolynomial.pderiv i B)
      ≤ (Work.Q44Geom.formPhi B).range := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    rw [Work.Q44Geom.formPhi_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, zero_smul]
    · intro hh; exact absurd (Finset.mem_univ i) hh
  have hrange_le : (Work.Q44Geom.formPhi B).range
      ≤ Submodule.span ℚ (Set.range fun i : Fin 5 => MvPolynomial.pderiv i B) := by
    intro y hy
    obtain ⟨w, rfl⟩ := hy
    rw [Work.Q44Geom.formPhi_apply]
    exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ (w i) (Submodule.subset_span (Set.mem_range_self i)))
  have hspan_eq : Submodule.span ℚ (Set.range fun i : Fin 5 => MvPolynomial.pderiv i B)
      = (Work.Q44Geom.formPhi B).range := le_antisymm hspan_le hrange_le
  have hrn := LinearMap.finrank_range_add_finrank_ker (Work.Q44Geom.formPhi B)
  rw [Module.finrank_fin_fun] at hrn
  by_contra hcon
  push_neg at hcon
  have hker_big : 4 ≤ Module.finrank ℚ ↥(Work.Q44Geom.formPhi B).ker :=
    le_trans hcon (Submodule.finrank_mono hker)
  have hrange_small : Module.finrank ℚ ↥(Work.Q44Geom.formPhi B).range ≤ 1 := by omega
  have hspan_small : Module.finrank ℚ
      (Submodule.span ℚ (Set.range fun i : Fin 5 => MvPolynomial.pderiv i B)) ≤ 1 := by
    rw [hspan_eq]; exact hrange_small
  exact false_of_cub_pderiv_span_finrank_le_one B hB hB0 hspan_small hnolin

end Work.HP.MDEstimates
