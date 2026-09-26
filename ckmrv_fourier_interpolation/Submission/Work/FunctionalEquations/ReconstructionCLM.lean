import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.Sampling.coeffs_continuous_linear
import Submission.Work.FunctionalEquations.SeminormGrowthOfRadialGrowth

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

/-!
# The reconstruction functional is continuous

The reconstruction formula of the CKMRV Fourier interpolation theorem expresses a radial
Schwartz function `f` as the sum `∑ i, (coeffs n 1 f i) • basis i` of its samples times the
interpolation basis.  In this file we show that the corresponding functional
`f ↦ ∑ i, (coeffs n 1 f i) * (basis i) x₀ - f x₀` is a continuous linear functional on the
complex Schwartz space.

The two analytic inputs are

* the coefficient samples `coeffs n 1 f i` decay faster than any polynomial in the index,
  uniformly in the Schwartz seminorms of `f` (`coeffs_seminorm_decay_family`), and
* the basis values `(basis i) x₀` grow at most polynomially in the index (the
  `growth_seminorm` field of `InterpolationSolution`).

Their product is then summable with a bound by finitely many Schwartz seminorms of `f`,
which is exactly the `mkCLMtoNormedSpace` criterion for a continuous linear functional on
the Schwartz space.
-/

/-- **Every Schwartz seminorm of the Fourier transform is bounded by finitely many Schwartz
seminorms of the function.**  This is the seminorm form of the continuity of
`FourierTransform.fourierCLM` on the Schwartz space. -/
theorem fourier_seminorm_le_family (n : ℕ) [NeZero n] (K L : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : 𝓢(E n, ℂ),
        (SchwartzMap.seminorm ℂ K L) (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f)
          ≤ C * s.sup (schwartzSeminormFamily ℂ (E n) ℂ) f := by
  obtain ⟨s, C, _hCne, hle⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (E n) ℂ)
    ((schwartzSeminormFamily ℂ (E n) ℂ (K, L)).comp
      ((FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))).toLinearMap))
    (by
      rw [Seminorm.coe_comp]
      exact ((schwartz_withSeminorms ℂ (E n) ℂ).continuous_seminorm (K, L)).comp
        (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))).continuous)
  refine ⟨s, C, C.coe_nonneg, fun f => ?_⟩
  have h := Seminorm.le_def.mp hle f
  rw [Seminorm.comp_apply] at h
  simp only [smul_apply] at h
  rwa [NNReal.smul_def, SchwartzMap.schwartzSeminormFamily_apply, smul_eq_mul] at h

/-- For `k ≥ 1` the polynomial weight `(k + 1) ^ N` is dominated by the Schwartz weight
`‖x‖ ^ (2 N)` at the sample point `x = realIncl (√(2 k))`. -/
lemma sample_weight_le {n : ℕ} [NeZero n] (N : ℕ) (k : Set.Ici (1 : ℕ)) :
    ((k.1 : ℝ) + 1) ^ N ≤ ‖realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ)))‖ ^ (2 * N) := by
  rw [Work.Sampling.realIncl_norm, abs_of_nonneg (Real.sqrt_nonneg _), pow_mul,
    Real.sq_sqrt (by positivity)]
  have hk : (1 : ℝ) ≤ (k.1 : ℝ) := by exact_mod_cast k.2
  exact pow_le_pow_left₀ (by positivity) (by linarith) N

/-- The value seminorm controls the values of `g` at the sample points, with the polynomial
weight `(k + 1) ^ N`. -/
lemma weight_mul_norm_sample_le {n : ℕ} [NeZero n] (N : ℕ) (k : Set.Ici (1 : ℕ))
    (g : 𝓢(E n, ℂ)) :
    ((k.1 : ℝ) + 1) ^ N * ‖g (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))‖
      ≤ (SchwartzMap.seminorm ℂ (2 * N) 0) g := by
  have hx := SchwartzMap.le_seminorm ℂ (2 * N) 0 g
    (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))
  rw [norm_iteratedFDeriv_zero] at hx
  exact le_trans (mul_le_mul_of_nonneg_right (sample_weight_le (n := n) N k) (norm_nonneg _)) hx

/-- The first derivative seminorm controls the directional derivatives of `g` at the sample
points, with the polynomial weight `(k + 1) ^ N`. -/
lemma weight_mul_norm_fderiv_le {n : ℕ} [NeZero n] (N : ℕ) (k : Set.Ici (1 : ℕ))
    (g : 𝓢(E n, ℂ)) :
    ((k.1 : ℝ) + 1) ^ N *
        ‖fderiv ℝ (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ)))) (realIncl (n := n) 1)‖
      ≤ (SchwartzMap.seminorm ℂ (2 * N) 1) g := by
  have hx := SchwartzMap.le_seminorm ℂ (2 * N) 1 g
    (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))
  rw [norm_iteratedFDeriv_one] at hx
  have hop : ‖fderiv ℝ (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ)))) (realIncl (n := n) 1)‖
      ≤ ‖fderiv ℝ (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))‖ := by
    calc ‖fderiv ℝ (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ)))) (realIncl (n := n) 1)‖
        ≤ ‖fderiv ℝ (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))‖ * ‖realIncl (n := n) 1‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))‖ := by
          rw [Work.Sampling.realIncl_norm_one, mul_one]
  calc ((k.1 : ℝ) + 1) ^ N *
        ‖fderiv ℝ (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ)))) (realIncl (n := n) 1)‖
      ≤ ((k.1 : ℝ) + 1) ^ N *
          ‖fderiv ℝ (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))‖ :=
        mul_le_mul_of_nonneg_left hop (by positivity)
    _ ≤ ‖realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ)))‖ ^ (2 * N) *
          ‖fderiv ℝ (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ))))‖ :=
        mul_le_mul_of_nonneg_right (sample_weight_le (n := n) N k) (norm_nonneg _)
    _ ≤ (SchwartzMap.seminorm ℂ (2 * N) 1) g := hx

/-! ### Explicit forms of the four samples -/

lemma coeffs_apply_zero {n : ℕ} [NeZero n] (f : 𝓢(E n, ℂ)) (k : Set.Ici (1 : ℕ)) :
    coeffs n 1 f (k, 0) = f (realIncl (n := n) (Real.sqrt (2 * (k : ℝ)))) := by
  simp [coeffs, Function.uncurry_apply_pair]

lemma coeffs_apply_one {n : ℕ} [NeZero n] (f : 𝓢(E n, ℂ)) (k : Set.Ici (1 : ℕ)) :
    coeffs n 1 f (k, 1)
      = (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f)
          (realIncl (n := n) (Real.sqrt (2 * (k : ℝ)))) := by
  simp [coeffs, Function.uncurry_apply_pair]

lemma coeffs_apply_two {n : ℕ} [NeZero n] (f : 𝓢(E n, ℂ)) (k : Set.Ici (1 : ℕ)) :
    coeffs n 1 f (k, 2)
      = fderiv ℝ (⇑f) (realIncl (n := n) (Real.sqrt (2 * (k : ℝ)))) (realIncl (n := n) 1) := by
  simp only [coeffs, Function.uncurry_apply_pair]
  exact Work.Sampling.deriv_comp_realIncl (SchwartzMap.hasFDerivAt f _)

lemma coeffs_apply_three {n : ℕ} [NeZero n] (f : 𝓢(E n, ℂ)) (k : Set.Ici (1 : ℕ)) :
    coeffs n 1 f (k, 3)
      = fderiv ℝ (⇑(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f))
          (realIncl (n := n) (Real.sqrt (2 * (k : ℝ)))) (realIncl (n := n) 1) := by
  simp only [coeffs, Function.uncurry_apply_pair]
  exact Work.Sampling.deriv_comp_realIncl (SchwartzMap.hasFDerivAt _ _)

/-! ### The decay of the samples -/

lemma slot_zero_le {n : ℕ} [NeZero n] (N : ℕ) (k : Set.Ici (1 : ℕ)) (f : 𝓢(E n, ℂ)) :
    ((k.1 : ℝ) + 1) ^ N * ‖coeffs n 1 f (k, 0)‖
      ≤ (SchwartzMap.seminorm ℂ (2 * N) 0) f := by
  rw [coeffs_apply_zero]
  exact weight_mul_norm_sample_le N k f

lemma slot_one_le {n : ℕ} [NeZero n] (N : ℕ) (k : Set.Ici (1 : ℕ)) (f : 𝓢(E n, ℂ)) :
    ((k.1 : ℝ) + 1) ^ N * ‖coeffs n 1 f (k, 1)‖
      ≤ (SchwartzMap.seminorm ℂ (2 * N) 0) (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f) := by
  rw [coeffs_apply_one]
  exact weight_mul_norm_sample_le N k _

lemma slot_two_le {n : ℕ} [NeZero n] (N : ℕ) (k : Set.Ici (1 : ℕ)) (f : 𝓢(E n, ℂ)) :
    ((k.1 : ℝ) + 1) ^ N * ‖coeffs n 1 f (k, 2)‖
      ≤ (SchwartzMap.seminorm ℂ (2 * N) 1) f := by
  rw [coeffs_apply_two]
  exact weight_mul_norm_fderiv_le N k f

lemma slot_three_le {n : ℕ} [NeZero n] (N : ℕ) (k : Set.Ici (1 : ℕ)) (f : 𝓢(E n, ℂ)) :
    ((k.1 : ℝ) + 1) ^ N * ‖coeffs n 1 f (k, 3)‖
      ≤ (SchwartzMap.seminorm ℂ (2 * N) 1) (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f) := by
  rw [coeffs_apply_three]
  exact weight_mul_norm_fderiv_le N k _

/-- **Polynomial decay of the CKMRV samples in the index, uniformly in finitely many
Schwartz seminorms.**  For every `N` there are finitely many Schwartz seminorms whose
supremum controls `(k + 1) ^ N * ‖coeffs n 1 f (k, j)‖` for every Schwartz function `f`
and every sample index `k ≥ 1`. -/
theorem coeffs_seminorm_decay_family (n : ℕ) [NeZero n] (N : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : 𝓢(E n, ℂ)) (i : SampleIdx 1),
        ((i.1.1 : ℝ) + 1) ^ N * ‖coeffs n 1 f i‖
          ≤ C * s.sup (schwartzSeminormFamily ℂ (E n) ℂ) f := by
  classical
  obtain ⟨s₀, C₀, hC₀, h₀⟩ := fourier_seminorm_le_family n (2 * N) 0
  obtain ⟨s₁, C₁, hC₁, h₁⟩ := fourier_seminorm_le_family n (2 * N) 1
  set S : Finset (ℕ × ℕ) := {(2 * N, 0), (2 * N, 1)} ∪ s₀ ∪ s₁ with hS
  set Cc : ℝ := max 1 (max C₀ C₁) with hCc
  have hCc1 : (1 : ℝ) ≤ Cc := by rw [hCc]; exact le_max_left _ _
  have hC0 : C₀ ≤ Cc := by
    rw [hCc]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hC1 : C₁ ≤ Cc := by
    rw [hCc]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨S, Cc, le_trans zero_le_one hCc1, fun f i => ?_⟩
  have hSf : 0 ≤ (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := apply_nonneg _ _
  have hmem : ∀ m ∈ S, (schwartzSeminormFamily ℂ (E n) ℂ m) f
      ≤ Cc * (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := by
    intro m hm
    have h1 : (schwartzSeminormFamily ℂ (E n) ℂ m) f
        ≤ (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
      Seminorm.le_def.mp (Finset.le_sup hm) f
    calc (schwartzSeminormFamily ℂ (E n) ℂ m) f
        ≤ (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := h1
      _ = 1 * (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := (one_mul _).symm
      _ ≤ Cc * (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
          mul_le_mul_of_nonneg_right hCc1 hSf
  have hs₀ : s₀ ⊆ S := by
    rw [hS]; intro x hx; exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hs₁ : s₁ ⊆ S := by
    rw [hS]; intro x hx; exact Finset.mem_union_right _ hx
  have h0sup : C₀ * (s₀.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f
      ≤ Cc * (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := by
    have hsup : (s₀.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f
        ≤ (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
      Seminorm.le_def.mp (Finset.sup_mono hs₀) f
    calc C₀ * (s₀.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f
        ≤ C₀ * (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
          mul_le_mul_of_nonneg_left hsup hC₀
      _ ≤ Cc * (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
          mul_le_mul_of_nonneg_right hC0 hSf
  have h1sup : C₁ * (s₁.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f
      ≤ Cc * (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := by
    have hsup : (s₁.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f
        ≤ (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
      Seminorm.le_def.mp (Finset.sup_mono hs₁) f
    calc C₁ * (s₁.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f
        ≤ C₁ * (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
          mul_le_mul_of_nonneg_left hsup hC₁
      _ ≤ Cc * (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f :=
          mul_le_mul_of_nonneg_right hC1 hSf
  have hzero : ∀ (k : Set.Ici (1 : ℕ)),
      ((k.1 : ℝ) + 1) ^ N * ‖coeffs n 1 f (k, 0)‖
        ≤ Cc * (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := by
    intro k
    refine le_trans (slot_zero_le N k f) ?_
    rw [← SchwartzMap.schwartzSeminormFamily_apply]
    exact hmem (2 * N, 0) (by rw [hS]; simp)
  have hone : ∀ (k : Set.Ici (1 : ℕ)),
      ((k.1 : ℝ) + 1) ^ N * ‖coeffs n 1 f (k, 1)‖
        ≤ Cc * (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := by
    intro k
    refine le_trans (slot_one_le N k f) ?_
    rw [← SchwartzMap.schwartzSeminormFamily_apply]
    exact le_trans (h₀ f) h0sup
  have htwo : ∀ (k : Set.Ici (1 : ℕ)),
      ((k.1 : ℝ) + 1) ^ N * ‖coeffs n 1 f (k, 2)‖
        ≤ Cc * (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := by
    intro k
    refine le_trans (slot_two_le N k f) ?_
    rw [← SchwartzMap.schwartzSeminormFamily_apply]
    exact hmem (2 * N, 1) (by rw [hS]; simp)
  have hthree : ∀ (k : Set.Ici (1 : ℕ)),
      ((k.1 : ℝ) + 1) ^ N * ‖coeffs n 1 f (k, 3)‖
        ≤ Cc * (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := by
    intro k
    refine le_trans (slot_three_le N k f) ?_
    rw [← SchwartzMap.schwartzSeminormFamily_apply]
    exact le_trans (h₁ f) h1sup
  obtain ⟨k, j⟩ := i
  fin_cases j
  · exact hzero k
  · exact hone k
  · exact htwo k
  · exact hthree k

/-- The weight `1 / (k + 1) ^ 2` is summable over the sample index. -/
lemma summable_sampleWeight_inv_sq :
    Summable (fun i : SampleIdx 1 => 1 / (((i.1.1 : ℝ) + 1) ^ 2)) := by
  have hbase : Summable fun m : ℕ => 1 / (((m : ℝ) + 1) ^ 2) := by
    have h2 : Summable fun m : ℕ => 1 / ((m : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow).mpr (by norm_num)
    have h3 : Summable fun m : ℕ => 1 / (((m + 1 : ℕ) : ℝ) ^ 2) :=
      (summable_nat_add_iff (f := fun m : ℕ => 1 / ((m : ℝ) ^ 2)) 1).mpr h2
    simpa [Nat.cast_add, Nat.cast_one] using h3
  have hsub : Summable fun m : Set.Ici (1 : ℕ) => 1 / (((m.1 : ℝ) + 1) ^ 2) :=
    hbase.subtype (fun m => 1 ≤ m)
  refine (summable_prod_of_nonneg
    (f := fun p : SampleIdx 1 => 1 / (((p.1.1 : ℝ) + 1) ^ 2)) (fun p => by positivity)).mpr
    ⟨fun _ => Summable.of_finite, ?_⟩
  have hconst : (fun x : Set.Ici (1 : ℕ) => ∑' _y : Fin 4, 1 / (((x.1 : ℝ) + 1) ^ 2))
      = fun x : Set.Ici (1 : ℕ) => 4 * (1 / (((x.1 : ℝ) + 1) ^ 2)) := by
    funext x
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  rw [hconst]
  exact hsub.mul_left 4

/-! ### The reconstruction series -/

/-- **The reconstruction series converges and is bounded by finitely many Schwartz
seminorms.**  This is the analytic content of the continuity of the reconstruction
functional. -/
theorem reconstruction_bound {n : ℕ} [NeZero n] (S : InterpolationSolution n) (x₀ : E n) :
    ∃ s : Finset (ℕ × ℕ), ∃ K : ℝ, 0 ≤ K ∧
      ∀ f : 𝓢(E n, ℂ),
        Summable (fun i : SampleIdx 1 => coeffs n 1 f i * (S.basis i).1 x₀) ∧
        ‖∑' i : SampleIdx 1, coeffs n 1 f i * (S.basis i).1 x₀‖
          ≤ K * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := by
  classical
  obtain ⟨Cb, Nb, hCb, hb⟩ := SeminormGrowthOfRadialGrowth S.basis S.growth_radial 0 0
  obtain ⟨s, Cc, hCc, hdecay⟩ := coeffs_seminorm_decay_family n (Nb + 2)
  have hSigmann : 0 ≤ ∑' i : SampleIdx 1, 1 / (((i.1.1 : ℝ) + 1) ^ 2) :=
    tsum_nonneg (fun i => by positivity)
  refine ⟨s, Cc * Cb * (∑' i : SampleIdx 1, 1 / (((i.1.1 : ℝ) + 1) ^ 2)),
    mul_nonneg (mul_nonneg hCc hCb) hSigmann, fun f => ?_⟩
  set Sf : ℝ := (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f with hSf
  have hSf0 : 0 ≤ Sf := by rw [hSf]; exact apply_nonneg _ _
  have hbound : ∀ i : SampleIdx 1,
      ‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖
        ≤ (Cc * Cb * Sf) * (1 / (((i.1.1 : ℝ) + 1) ^ 2)) := by
    intro i
    set D : ℝ := (i.1.1 : ℝ) + 1 with hD
    have hDpos : 0 < D := by rw [hD]; positivity
    have hDpow : 0 < D ^ Nb := pow_pos hDpos _
    have h1 : D ^ (Nb + 2) * ‖coeffs n 1 f i‖ ≤ Cc * Sf := by
      rw [hD, hSf]; exact hdecay f i
    have h2 : ‖(S.basis i).1 x₀‖ ≤ Cb * D ^ Nb := by
      refine le_trans (SchwartzMap.norm_le_seminorm ℂ (S.basis i).1 x₀) ?_
      rw [hD]
      exact hb i.1 i.2
    have h3 : D ^ (Nb + 2) * (‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖)
        ≤ (Cc * Sf) * (Cb * D ^ Nb) := by
      calc D ^ (Nb + 2) * (‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖)
          = (D ^ (Nb + 2) * ‖coeffs n 1 f i‖) * ‖(S.basis i).1 x₀‖ := by ring
        _ ≤ (Cc * Sf) * ‖(S.basis i).1 x₀‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ (Cc * Sf) * (Cb * D ^ Nb) := mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : D ^ Nb * (D ^ 2 * (‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖))
        ≤ D ^ Nb * (Cc * Cb * Sf) := by
      calc D ^ Nb * (D ^ 2 * (‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖))
          = D ^ (Nb + 2) * (‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖) := by
            rw [pow_add]; ring
        _ ≤ (Cc * Sf) * (Cb * D ^ Nb) := h3
        _ = D ^ Nb * (Cc * Cb * Sf) := by ring
    have h5 : D ^ 2 * (‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖) ≤ Cc * Cb * Sf :=
      (mul_le_mul_iff_of_pos_left hDpow).mp h4
    have h6 : ‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖ ≤ (Cc * Cb * Sf) * (1 / D ^ 2) := by
      rw [mul_one_div, le_div_iff₀ (by positivity : (0 : ℝ) < D ^ 2)]
      calc (‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖) * D ^ 2
          = D ^ 2 * (‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖) := by ring
        _ ≤ Cc * Cb * Sf := h5
    rwa [hD] at h6
  have hsum_norm : Summable (fun i : SampleIdx 1 => ‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hbound
      (summable_sampleWeight_inv_sq.mul_left (Cc * Cb * Sf))
  have hsum_f : Summable (fun i : SampleIdx 1 => coeffs n 1 f i * (S.basis i).1 x₀) :=
    Summable.of_norm_bounded hsum_norm (fun i => le_of_eq (norm_mul _ _))
  refine ⟨hsum_f, ?_⟩
  calc ‖∑' i : SampleIdx 1, coeffs n 1 f i * (S.basis i).1 x₀‖
      ≤ ∑' i : SampleIdx 1, ‖coeffs n 1 f i * (S.basis i).1 x₀‖ :=
        norm_tsum_le_tsum_norm hsum_f.norm
    _ = ∑' i : SampleIdx 1, ‖coeffs n 1 f i‖ * ‖(S.basis i).1 x₀‖ :=
        tsum_congr (fun i => norm_mul _ _)
    _ ≤ ∑' i : SampleIdx 1, (Cc * Cb * Sf) * (1 / (((i.1.1 : ℝ) + 1) ^ 2)) :=
        Summable.tsum_le_tsum hbound hsum_norm
          (summable_sampleWeight_inv_sq.mul_left (Cc * Cb * Sf))
    _ = (Cc * Cb * Sf) * ∑' i : SampleIdx 1, 1 / (((i.1.1 : ℝ) + 1) ^ 2) := tsum_mul_left
    _ = (Cc * Cb * (∑' i : SampleIdx 1, 1 / (((i.1.1 : ℝ) + 1) ^ 2)))
          * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := by rw [hSf]; ring

/-- **The reconstruction functional is continuous.**  For a solution `S` of the functional
equations and a point `x₀`, the map `f ↦ ∑ i, (coeffs n 1 f i) * (basis i) x₀ - f x₀` is a
continuous linear functional on the complex Schwartz space. -/
theorem ReconstructionCLM {n : ℕ} [NeZero n] (S : InterpolationSolution n) (x₀ : E n) :
    ∃ Λ : 𝓢(E n, ℂ) →L[ℂ] ℂ, ∀ f : 𝓢(E n, ℂ),
      Λ f = (∑' i : SampleIdx 1, coeffs n 1 f i * (S.basis i).1 x₀) - f x₀ := by
  classical
  obtain ⟨C, hC⟩ := Work.Sampling.coeffs_continuous_linear n 1
  obtain ⟨s, K, hK, hb⟩ := reconstruction_bound S x₀
  have hcoeffs_add : ∀ f g : 𝓢(E n, ℂ),
      coeffs n 1 (f + g) = coeffs n 1 f + coeffs n 1 g := by
    intro f g; rw [← hC (f + g), ← hC f, ← hC g, map_add]
  have hcoeffs_smul : ∀ (a : ℂ) (f : 𝓢(E n, ℂ)),
      coeffs n 1 (a • f) = a • coeffs n 1 f := by
    intro a f; rw [← hC (a • f), ← hC f, map_smul]
  have hadd : ∀ f g : 𝓢(E n, ℂ),
      (∑' i : SampleIdx 1, coeffs n 1 (f + g) i * (S.basis i).1 x₀)
        = (∑' i : SampleIdx 1, coeffs n 1 f i * (S.basis i).1 x₀)
          + (∑' i : SampleIdx 1, coeffs n 1 g i * (S.basis i).1 x₀) := by
    intro f g
    rw [hcoeffs_add f g]
    simp only [Pi.add_apply, add_mul]
    exact Summable.tsum_add (hb f).1 (hb g).1
  have hsmul : ∀ (a : ℂ) (f : 𝓢(E n, ℂ)),
      (∑' i : SampleIdx 1, coeffs n 1 (a • f) i * (S.basis i).1 x₀)
        = a • (∑' i : SampleIdx 1, coeffs n 1 f i * (S.basis i).1 x₀) := by
    intro a f
    have hcf : ∀ i, coeffs n 1 (a • f) i = a * coeffs n 1 f i := by
      intro i
      simpa [Pi.smul_apply, smul_eq_mul] using congrFun (hcoeffs_smul a f) i
    simp only [hcf, mul_assoc]
    rw [tsum_mul_left, smul_eq_mul]
  have hbnd : ∃ s' : Finset (ℕ × ℕ), ∃ C' : ℝ, 0 ≤ C' ∧ ∀ f : 𝓢(E n, ℂ),
      ‖∑' i : SampleIdx 1, coeffs n 1 f i * (S.basis i).1 x₀‖
        ≤ C' * s'.sup (schwartzSeminormFamily ℂ (E n) ℂ) f :=
    ⟨s, K, hK, fun f => (hb f).2⟩
  let A : 𝓢(E n, ℂ) →L[ℂ] ℂ :=
    SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ) (𝕜' := ℂ) (D := E n) (E := ℂ) (G := ℂ)
      (σ := RingHom.id ℂ)
      (fun f => ∑' i : SampleIdx 1, coeffs n 1 f i * (S.basis i).1 x₀) hadd hsmul hbnd
  refine ⟨A - Work.Sampling.evalAtCLM x₀, fun f => ?_⟩
  rw [sub_apply, Work.Sampling.evalAtCLM_apply]
  rfl

end

end Work.FunctionalEquations
