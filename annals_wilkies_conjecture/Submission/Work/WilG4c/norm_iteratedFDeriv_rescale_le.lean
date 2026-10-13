import Mathlib

namespace Work.WilG4c

open scoped Topology

/-- Affine rescaling of the iterated derivative: for `lam > 0` the translated rescaling
`y ↦ h ((v + y)/lam)` has `m`-th iterated derivative at `x` bounded by the `m`-th iterated
derivative of `h` at `(v + x)/lam` times `lam⁻¹ ^ m`.  No smoothness of `h` is needed: for an
affine reparametrisation all Faà di Bruno corrections vanish, and the corresponding Mathlib
chain rule for composition with a continuous linear equivalence is unconditional. -/
theorem norm_iteratedFDeriv_rescale_le {N : ℕ} (lam : ℝ) (hlam : 0 < lam)
    (h : (Fin N → ℝ) → ℝ) (v x : Fin N → ℝ) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y : Fin N → ℝ => h (fun i => (v i + y i) / lam)) x‖
      ≤ ‖iteratedFDeriv ℝ m h (fun i => (v i + x i) / lam)‖ * lam⁻¹ ^ m := by
  have hne : lam ≠ 0 := ne_of_gt hlam
  -- The linear part `y ↦ y / lam` of the reparametrisation, as a continuous linear equivalence.
  let A : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) :=
    ContinuousLinearEquiv.equivOfInverse
      (lam⁻¹ • (1 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)))
      (lam • (1 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)))
      (fun y => by
        show (lam • (1 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)))
            ((lam⁻¹ • (1 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) y) = y
        rw [smul_apply, smul_apply, one_apply_eq_self, one_apply_eq_self, smul_smul,
          mul_inv_cancel₀ hne, one_smul])
      (fun y => by
        show (lam⁻¹ • (1 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)))
            ((lam • (1 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) y) = y
        rw [smul_apply, smul_apply, one_apply_eq_self, one_apply_eq_self, smul_smul,
          inv_mul_cancel₀ hne, one_smul])
  have hAcoe : (A : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))
      = lam⁻¹ • (1 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) := rfl
  have happ : ∀ y : Fin N → ℝ, A y = fun i => y i / lam := by
    intro y
    change (lam⁻¹ • (1 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) y = fun i => y i / lam
    ext i; simp [div_eq_inv_mul]
  have hAnorm : ‖(A : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))‖ ≤ lam⁻¹ := by
    rw [hAcoe, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hlam.le)]
    calc lam⁻¹ * ‖(1 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))‖ ≤ lam⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_nonneg.mpr hlam.le)
      _ = lam⁻¹ := by ring
  -- The constant `v / lam` of the affine reparametrisation.
  set c : Fin N → ℝ := fun i => v i / lam with hc_def
  -- Rewrite the rescaled function as `(fun z => h (c + z)) ∘ A`.
  have hfun : (fun y : Fin N → ℝ => h (fun i => (v i + y i) / lam))
      = (fun z : Fin N → ℝ => h (c + z)) ∘ A := by
    funext y
    simp only [Function.comp_apply]
    congr 1
    ext i
    show (v i + y i) / lam = (c + A y) i
    rw [Pi.add_apply, hc_def, happ y]
    simp only [div_eq_mul_inv]
    ring
  have hcx : c + A x = fun i => (v i + x i) / lam := by
    ext i
    show (c + A x) i = (v i + x i) / lam
    rw [Pi.add_apply, hc_def, happ x]
    simp only [div_eq_mul_inv]
    ring
  -- Chain rule for composition with the continuous linear equivalence `A` (no differentiability
  -- of `h` needed), and the translation invariance for the constant shift by `c`.
  have hchain : iteratedFDeriv ℝ m ((fun z : Fin N → ℝ => h (c + z)) ∘ A) x
      = (iteratedFDeriv ℝ m (fun z : Fin N → ℝ => h (c + z)) (A x)).compContinuousLinearMap
          (fun _ : Fin m => (A : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) := by
    have hw := ContinuousLinearEquiv.iteratedFDerivWithin_comp_right (𝕜 := ℝ) A
      (fun z : Fin N → ℝ => h (c + z)) (s := Set.univ) uniqueDiffOn_univ (Set.mem_univ (A x)) m
    simpa only [Set.preimage_univ, iteratedFDerivWithin_univ] using hw
  have hshift : iteratedFDeriv ℝ m (fun z : Fin N → ℝ => h (c + z)) (A x)
      = iteratedFDeriv ℝ m h (c + A x) := iteratedFDeriv_comp_add_left m c (A x)
  calc
    ‖iteratedFDeriv ℝ m (fun y : Fin N → ℝ => h (fun i => (v i + y i) / lam)) x‖
        = ‖iteratedFDeriv ℝ m ((fun z : Fin N → ℝ => h (c + z)) ∘ A) x‖ := by rw [hfun]
      _ = ‖(iteratedFDeriv ℝ m (fun z : Fin N → ℝ => h (c + z)) (A x)).compContinuousLinearMap
            (fun _ : Fin m => (A : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)))‖ := by rw [hchain]
      _ ≤ ‖iteratedFDeriv ℝ m (fun z : Fin N → ℝ => h (c + z)) (A x)‖ *
            ‖(A : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))‖ ^ m := by
          simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
            (ContinuousMultilinearMap.norm_compContinuousLinearMap_le
              (iteratedFDeriv ℝ m (fun z : Fin N → ℝ => h (c + z)) (A x))
              (fun _ : Fin m => (A : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))))
      _ = ‖iteratedFDeriv ℝ m h (c + A x)‖ *
            ‖(A : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))‖ ^ m := by rw [hshift]
      _ ≤ ‖iteratedFDeriv ℝ m h (c + A x)‖ * lam⁻¹ ^ m :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hAnorm m) (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ m h (fun i => (v i + x i) / lam)‖ * lam⁻¹ ^ m := by rw [hcx]

end Work.WilG4c
