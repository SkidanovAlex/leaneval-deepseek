import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.Sampling.rapidlyDecreasing_coeffs

/-!
# Uniform polynomial decay of the CKMRV samples

For a complex Schwartz function `f` on `R^n`, the samples `coeffs n 1 f i` (the values of `f`
and of its Fourier transform, and the radial derivatives of both, at the radii `sqrt (2k)`,
`k >= 1`) are not merely rapidly decreasing: the decay is *uniform* in the index, in the sense
that the weighted samples `(k+1)^N * |coeffs n 1 f i|` are all bounded by a single constant
times a single finite supremum of Schwartz seminorms of `f`.

More precisely we prove, for every `N`,

`∃ s C, 0 ≤ C ∧ ∀ f i, ((i.1.1 : ℝ) + 1)^N * ‖coeffs n 1 f i‖ ≤ C * s.sup F f`

where `F = schwartzSeminormFamily ℂ E ℂ` and `E = EuclideanSpace ℝ (Fin n)`.

The three ingredients of the proof are:

* the weight `(k+1)^N` is dominated by `‖x_k‖^(2N+2)`, where `x_k = realIncl (√(2k))` has norm
  `√(2k)`, because `(k+1)^N ≤ (2k)^(N+1) = ‖x_k‖^(2N+2)` for `k ≥ 1`; hence the two samples of
  `f` itself are bounded by `SchwartzMap.seminorm ℂ (2N+2) 0 f` and
  `SchwartzMap.seminorm ℂ (2N+2) 1 f`;
* the same estimate may be applied to the Fourier transform `f̂`, which is again Schwartz;
* a finite supremum of Schwartz seminorms controls `SchwartzMap.seminorm ℂ m l f̂` for every
  `m` and `l`, by continuity of the Fourier transform together with continuity of the seminorms
  (`Seminorm.bound_of_continuous`).
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

/-! ## The weight is dominated by the `(2N+2)`-th power of the sample radius -/

/-- For `k ≥ 1`, the weight `(1 + k)^N` is bounded by the `(2N+2)`-th power of the norm of the
sample point `realIncl (sqrt (2k))`, which equals `sqrt (2k)`. -/
lemma coeffsSeminormDecay_weight_le (n : ℕ) [NeZero n] (N : ℕ) (k : Set.Ici (1 : ℕ)) :
    ((k.1 : ℝ) + 1) ^ N ≤ ‖realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ)))‖ ^ (2 * N + 2) := by
  have hk : (1 : ℝ) ≤ (k.1 : ℝ) := by exact_mod_cast k.2
  have hnorm : ‖realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ)))‖ = Real.sqrt (2 * (k.1 : ℝ)) := by
    rw [Work.Sampling.realIncl_norm, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [hnorm]
  have hpow : (Real.sqrt (2 * (k.1 : ℝ))) ^ (2 * N + 2) = (2 * (k.1 : ℝ)) ^ (N + 1) := by
    rw [show 2 * N + 2 = 2 * (N + 1) from by ring, pow_mul, Real.sq_sqrt (by positivity)]
  rw [hpow]
  calc ((k.1 : ℝ) + 1) ^ N ≤ (2 * (k.1 : ℝ)) ^ N :=
        pow_le_pow_left₀ (by positivity) (by linarith) N
    _ ≤ (2 * (k.1 : ℝ)) ^ (N + 1) :=
        pow_le_pow_right₀ (by linarith) (Nat.le_succ N)

/-! ## The weighted samples of a Schwartz function -/

/-- The weighted value samples of a Schwartz function at the sample points are controlled by the
Schwartz seminorm of weight `2N+2`. -/
lemma coeffsSeminormDecay_value (n : ℕ) [NeZero n] (N : ℕ) (g : 𝓢(E n, ℂ))
    (k : Set.Ici (1 : ℕ)) :
    ((k.1 : ℝ) + 1) ^ N * ‖g (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))‖
      ≤ (SchwartzMap.seminorm ℂ (2 * N + 2) 0) g := by
  refine le_trans (mul_le_mul_of_nonneg_right (coeffsSeminormDecay_weight_le n N k)
    (norm_nonneg _)) ?_
  exact SchwartzMap.norm_pow_mul_le_seminorm ℂ g (2 * N + 2) _

/-- The weighted radial-derivative samples of a Schwartz function at the sample points are
controlled by the Schwartz seminorm of weight `2N+2` and order `1`. -/
lemma coeffsSeminormDecay_deriv (n : ℕ) [NeZero n] (N : ℕ) (g : 𝓢(E n, ℂ))
    (k : Set.Ici (1 : ℕ)) :
    ((k.1 : ℝ) + 1) ^ N * ‖deriv (g ∘ realIncl (n := n)) (Real.sqrt (2 * (k.1 : ℝ)))‖
      ≤ (SchwartzMap.seminorm ℂ (2 * N + 2) 1) g := by
  have hderiv : deriv (g ∘ realIncl (n := n)) (Real.sqrt (2 * (k.1 : ℝ)))
      = fderiv ℝ (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ)))) (realIncl (n := n) 1) :=
    Work.Sampling.deriv_comp_realIncl (SchwartzMap.hasFDerivAt g _)
  have hstep : ‖fderiv ℝ (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))
        (realIncl (n := n) 1)‖
      ≤ ‖iteratedFDeriv ℝ 1 (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))‖ := by
    rw [norm_iteratedFDeriv_one]
    calc ‖fderiv ℝ (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ)))) (realIncl (n := n) 1)‖
        ≤ ‖fderiv ℝ (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))‖ *
            ‖realIncl (n := n) 1‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))‖ := by
          rw [Work.Sampling.realIncl_norm_one, mul_one]
  calc ((k.1 : ℝ) + 1) ^ N * ‖deriv (g ∘ realIncl (n := n)) (Real.sqrt (2 * (k.1 : ℝ)))‖
      = ((k.1 : ℝ) + 1) ^ N *
          ‖fderiv ℝ (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ)))) (realIncl (n := n) 1)‖ := by
        rw [hderiv]
    _ ≤ ‖realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ)))‖ ^ (2 * N + 2) *
          ‖fderiv ℝ (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ)))) (realIncl (n := n) 1)‖ :=
        mul_le_mul_of_nonneg_right (coeffsSeminormDecay_weight_le n N k) (norm_nonneg _)
    _ ≤ ‖realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ)))‖ ^ (2 * N + 2) *
          ‖iteratedFDeriv ℝ 1 (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))‖ :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ ≤ (SchwartzMap.seminorm ℂ (2 * N + 2) 1) g :=
        SchwartzMap.le_seminorm ℂ (2 * N + 2) 1 g _

/-! ## Seminorm bounds for the Fourier transform -/

/-- **The Fourier transform is controlled by finitely many Schwartz seminorms.**  For every pair
of indices `(m, l)` there is a finite set of Schwartz seminorms and a constant bounding
`SchwartzMap.seminorm ℂ m l (f̂)` for every Schwartz function `f`.

This is `Seminorm.bound_of_continuous` applied to the continuous seminorm
`f ↦ seminorm ℂ m l (f̂)`, using continuity of the Fourier transform. -/
lemma coeffsSeminormDecay_fourierSeminorm (n : ℕ) [NeZero n] (m l : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : 𝓢(E n, ℂ),
        (SchwartzMap.seminorm ℂ m l) (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) g)
          ≤ C * s.sup (schwartzSeminormFamily ℂ (E n) ℂ) g := by
  classical
  let T : 𝓢(E n, ℂ) →ₗ[ℂ] 𝓢(E n, ℂ) :=
    (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))).toLinearMap
  let q : Seminorm ℂ 𝓢(E n, ℂ) := (SchwartzMap.seminorm ℂ m l).comp T
  have hq : Continuous ⇑q := by
    change Continuous fun g : 𝓢(E n, ℂ) =>
      (SchwartzMap.seminorm ℂ m l) (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) g)
    exact ((WithSeminorms.continuous_seminorm
        (schwartz_withSeminorms ℂ (E n) ℂ) (m, l)).comp
      (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))).continuous)
  obtain ⟨s, C, _hC, hle⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (E n) ℂ) q hq
  refine ⟨s, (C : ℝ), C.coe_nonneg, fun g => ?_⟩
  have h := Seminorm.le_def.mp hle g
  change (SchwartzMap.seminorm ℂ m l) (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) g)
    ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) g
  rw [smul_apply, NNReal.smul_def, smul_eq_mul] at h
  exact h

/-- The weighted value samples of the Fourier transform of a Schwartz function are controlled by
a finite supremum of Schwartz seminorms of the function. -/
lemma coeffsSeminormDecay_fourierValue (n : ℕ) [NeZero n] (N : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : 𝓢(E n, ℂ)) (k : Set.Ici (1 : ℕ)),
        ((k.1 : ℝ) + 1) ^ N *
          ‖(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) g)
              (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))‖
          ≤ C * s.sup (schwartzSeminormFamily ℂ (E n) ℂ) g := by
  obtain ⟨s, C, hC, hle⟩ := coeffsSeminormDecay_fourierSeminorm (n := n) (2 * N + 2) 0
  exact ⟨s, C, hC, fun g k =>
    (coeffsSeminormDecay_value n N (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) g) k).trans
      (hle g)⟩

/-- The weighted radial-derivative samples of the Fourier transform of a Schwartz function are
controlled by a finite supremum of Schwartz seminorms of the function. -/
lemma coeffsSeminormDecay_fourierDeriv (n : ℕ) [NeZero n] (N : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : 𝓢(E n, ℂ)) (k : Set.Ici (1 : ℕ)),
        ((k.1 : ℝ) + 1) ^ N *
          ‖deriv ((FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) g) ∘ realIncl (n := n))
              (Real.sqrt (2 * (k.1 : ℝ)))‖
          ≤ C * s.sup (schwartzSeminormFamily ℂ (E n) ℂ) g := by
  obtain ⟨s, C, hC, hle⟩ := coeffsSeminormDecay_fourierSeminorm (n := n) (2 * N + 2) 1
  exact ⟨s, C, hC, fun g k =>
    (coeffsSeminormDecay_deriv n N (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) g) k).trans
      (hle g)⟩

/-! ## The uniform decay of the CKMRV samples -/

theorem CoeffsSeminormDecayFamily (n : ℕ) [NeZero n] (N : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (i : Set.Ici (1:ℕ) × Fin 4),
        ((i.1.1 : ℝ) + 1) ^ N *
            ‖LeanEval.Analysis.CKMRVInterpolation.coeffs n 1 f i‖
          ≤ C * s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n)) ℂ) f := by
  classical
  obtain ⟨sfv, Cfv, hCfv, hfv⟩ := coeffsSeminormDecay_fourierValue (n := n) N
  obtain ⟨sfd, Cfd, hCfd, hfd⟩ := coeffsSeminormDecay_fourierDeriv (n := n) N
  set s : Finset (ℕ × ℕ) := {(2 * N + 2, 0), (2 * N + 2, 1)} ∪ sfv ∪ sfd with hs
  set C : ℝ := max (max 1 Cfv) Cfd with hCdef
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one (le_trans (le_max_left 1 Cfv) (le_max_left _ _))
  have honeC : (1 : ℝ) ≤ C := le_trans (le_max_left 1 Cfv) (le_max_left _ _)
  have hCfvC : Cfv ≤ C := le_trans (le_max_right 1 Cfv) (le_max_left _ _)
  have hCfdC : Cfd ≤ C := le_max_right _ _
  refine ⟨s, C, hC0, ?_⟩
  intro f i
  obtain ⟨k, j⟩ := i
  -- membership of the two plain seminorms in the chosen finite set
  have hmem0 : ((2 * N + 2, 0) : ℕ × ℕ) ∈ s := by rw [hs]; simp
  have hmem1 : ((2 * N + 2, 1) : ℕ × ℕ) ∈ s := by rw [hs]; simp
  have hsup0 : (schwartzSeminormFamily ℂ (E n) ℂ (2 * N + 2, 0)) f
      ≤ (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
    Seminorm.le_def.mp (Finset.le_sup (f := schwartzSeminormFamily ℂ (E n) ℂ) hmem0) f
  have hsup1 : (schwartzSeminormFamily ℂ (E n) ℂ (2 * N + 2, 1)) f
      ≤ (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
    Seminorm.le_def.mp (Finset.le_sup (f := schwartzSeminormFamily ℂ (E n) ℂ) hmem1) f
  -- the two Fourier seminorm suprema are dominated by the chosen one
  have hsfv : (sfv.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f
      ≤ (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
    Seminorm.le_def.mp (Finset.sup_le fun p hp =>
      Finset.le_sup (f := schwartzSeminormFamily ℂ (E n) ℂ) (by rw [hs]; simp [hp])) f
  have hsfd : (sfd.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f
      ≤ (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
    Seminorm.le_def.mp (Finset.sup_le fun p hp =>
      Finset.le_sup (f := schwartzSeminormFamily ℂ (E n) ℂ) (by rw [hs]; simp [hp])) f
  have hnn : (0 : ℝ) ≤ (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
    NonnegHomClass.apply_nonneg (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f
  fin_cases j
  · change ((k.1 : ℝ) + 1) ^ N * ‖f (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))‖
        ≤ C * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f
    calc ((k.1 : ℝ) + 1) ^ N * ‖f (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))‖
        ≤ (SchwartzMap.seminorm ℂ (2 * N + 2) 0) f := coeffsSeminormDecay_value n N f k
      _ = (schwartzSeminormFamily ℂ (E n) ℂ (2 * N + 2, 0)) f := rfl
      _ ≤ (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := hsup0
      _ = 1 * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := (one_mul _).symm
      _ ≤ C * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
          mul_le_mul_of_nonneg_right honeC hnn
  · change ((k.1 : ℝ) + 1) ^ N *
          ‖(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f)
            (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))‖
        ≤ C * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f
    calc ((k.1 : ℝ) + 1) ^ N *
          ‖(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f)
            (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))‖
        ≤ Cfv * (sfv.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := hfv f k
      _ ≤ Cfv * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
          mul_le_mul_of_nonneg_left hsfv hCfv
      _ ≤ C * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
          mul_le_mul_of_nonneg_right hCfvC hnn
  · change ((k.1 : ℝ) + 1) ^ N *
          ‖deriv (f ∘ realIncl (n := n)) (Real.sqrt (2 * (k.1 : ℝ)))‖
        ≤ C * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f
    calc ((k.1 : ℝ) + 1) ^ N * ‖deriv (f ∘ realIncl (n := n)) (Real.sqrt (2 * (k.1 : ℝ)))‖
        ≤ (SchwartzMap.seminorm ℂ (2 * N + 2) 1) f := coeffsSeminormDecay_deriv n N f k
      _ = (schwartzSeminormFamily ℂ (E n) ℂ (2 * N + 2, 1)) f := rfl
      _ ≤ (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := hsup1
      _ = 1 * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := (one_mul _).symm
      _ ≤ C * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
          mul_le_mul_of_nonneg_right honeC hnn
  · change ((k.1 : ℝ) + 1) ^ N *
          ‖deriv ((FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f) ∘ realIncl (n := n))
            (Real.sqrt (2 * (k.1 : ℝ)))‖
        ≤ C * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f
    calc ((k.1 : ℝ) + 1) ^ N *
          ‖deriv ((FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f) ∘ realIncl (n := n))
            (Real.sqrt (2 * (k.1 : ℝ)))‖
        ≤ Cfd * (sfd.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := hfd f k
      _ ≤ Cfd * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
          mul_le_mul_of_nonneg_left hsfd hCfd
      _ ≤ C * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
          mul_le_mul_of_nonneg_right hCfdC hnn

end

end Work.FunctionalEquations
