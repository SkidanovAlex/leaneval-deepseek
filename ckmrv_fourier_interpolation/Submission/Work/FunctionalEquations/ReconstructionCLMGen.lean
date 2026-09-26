import Mathlib
import Submission.Work.FunctionalEquations.Gen
import Submission.Work.FunctionalEquations.ReconstructionCLM
import Submission.Work.FunctionalEquations.SeminormGrowthOfRadialGrowth

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

set_option maxHeartbeats 1000000

/-!
# The reconstruction functional is continuous, in the general-`k₀` setting

This is the `k₀`-general companion of `Work.FunctionalEquations.ReconstructionCLM`.
For an `InterpolationSolutionGen n k₀` the reconstruction series
`f ↦ ∑ i, (coeffs n k₀ f i) * (basis i) x₀` is (together with the evaluation of `f` at
`x₀`) a continuous linear functional on the complex Schwartz space.

The two analytic inputs are the same as in the `k₀ = 1` case:

* the coefficient samples `coeffs n k₀ f i` decay faster than any polynomial in the index,
  uniformly in the Schwartz seminorms of `f` (`coeffs_seminorm_decay_family_gen` below), and
* the basis values `(basis i) x₀` grow at most polynomially in the index
  (the `growth_seminorm` field of `InterpolationSolutionGen`).

Everything is stated for arbitrary `k₀ : ℕ`.  The only place where the index matters is
the comparison between the polynomial weight `(k+1)^N` and the Schwartz weight
`‖realIncl (√(2k))‖^{2N}`: for `k ≥ 1` the first is dominated by the second, while for
`k = 0` the norm vanishes, so a supplementary factor `max 1 ‖·‖^{2N}` is used.  This
makes the estimates uniform in the index.
-/

/-! ### The polynomial weight against the Schwartz weight -/

/-- For every index `k` and every `N`, the polynomial weight `(k+1)^N` is at most `2^N`
times the larger of `1` and the `2N`-th power of `‖realIncl (√(2k))‖`.  The factor
`max 1 ‖·‖^{2N}` is only needed to cover the index `k = 0`, where the norm vanishes;
for `k ≥ 1` the bound reduces to `(k+1)^N ≤ 2^N ‖realIncl (√(2k))‖^{2N}`. -/
lemma sample_weight_le_all {n : ℕ} [NeZero n] (N k : ℕ) :
    ((k : ℝ) + 1) ^ N
      ≤ 2 ^ N * max 1 (‖realIncl (n := n) (Real.sqrt (2 * (k : ℝ)))‖ ^ (2 * N)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hnorm :
        ‖realIncl (n := n) (Real.sqrt (2 * ((0 : ℕ) : ℝ)))‖ ^ (2 * N) = (0 : ℝ) ^ (2 * N) := by
      rw [Work.Sampling.realIncl_norm, abs_of_nonneg (Real.sqrt_nonneg _)]
      norm_num
    have hle1 : (0 : ℝ) ^ (2 * N) ≤ 1 := pow_le_one₀ (le_refl 0) (by norm_num)
    rw [hnorm, max_eq_left hle1, mul_one]
    simp only [Nat.cast_zero, zero_add, one_pow]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hstep : ((k : ℝ) + 1) ^ N ≤ (2 * (k : ℝ)) ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith) N
    have hnorm :
        ‖realIncl (n := n) (Real.sqrt (2 * (k : ℝ)))‖ ^ (2 * N) = (2 * (k : ℝ)) ^ N := by
      rw [Work.Sampling.realIncl_norm, abs_of_nonneg (Real.sqrt_nonneg _), pow_mul,
        Real.sq_sqrt (by positivity)]
    rw [hnorm]
    have hmaxa : (2 * (k : ℝ)) ^ N ≤ max 1 ((2 * (k : ℝ)) ^ N) := le_max_right _ _
    have hmaxnn : 0 ≤ max 1 ((2 * (k : ℝ)) ^ N) := le_trans zero_le_one (le_max_left _ _)
    have hpow1 : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    calc ((k : ℝ) + 1) ^ N ≤ (2 * (k : ℝ)) ^ N := hstep
      _ ≤ max 1 ((2 * (k : ℝ)) ^ N) := hmaxa
      _ = 1 * max 1 ((2 * (k : ℝ)) ^ N) := (one_mul _).symm
      _ ≤ 2 ^ N * max 1 ((2 * (k : ℝ)) ^ N) := mul_le_mul_of_nonneg_right hpow1 hmaxnn

/-- The value seminorm controls the values of `g` at every sample point, with the
polynomial weight `(k + 1) ^ N`, uniformly in the index. -/
lemma weight_mul_norm_sample_le_all {n : ℕ} [NeZero n] (N : ℕ) (k : ℕ) (g : 𝓢(E n, ℂ)) :
    ((k : ℝ) + 1) ^ N * ‖g (realIncl (n := n) (Real.sqrt (2 * (k : ℝ))))‖
      ≤ 2 ^ N * ((SchwartzMap.seminorm ℂ 0 0) g + (SchwartzMap.seminorm ℂ (2 * N) 0) g) := by
  set x : E n := realIncl (n := n) (Real.sqrt (2 * (k : ℝ))) with hx
  have hw := sample_weight_le_all (n := n) N k
  rw [← hx] at hw
  have hmaxle : max 1 (‖x‖ ^ (2 * N)) ≤ 1 + ‖x‖ ^ (2 * N) := by
    refine max_le ?_ ?_
    · linarith [pow_nonneg (norm_nonneg x) (2 * N)]
    · linarith
  have h1 : max 1 (‖x‖ ^ (2 * N)) * ‖g x‖ ≤ (1 + ‖x‖ ^ (2 * N)) * ‖g x‖ :=
    mul_le_mul_of_nonneg_right hmaxle (norm_nonneg _)
  have h2 : ‖g x‖ ≤ (SchwartzMap.seminorm ℂ 0 0) g := SchwartzMap.norm_le_seminorm ℂ g x
  have h3 : ‖x‖ ^ (2 * N) * ‖g x‖ ≤ (SchwartzMap.seminorm ℂ (2 * N) 0) g := by
    have := SchwartzMap.le_seminorm ℂ (2 * N) 0 g x
    rwa [norm_iteratedFDeriv_zero] at this
  calc ((k : ℝ) + 1) ^ N * ‖g x‖
      ≤ (2 ^ N * max 1 (‖x‖ ^ (2 * N))) * ‖g x‖ :=
        mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ = 2 ^ N * (max 1 (‖x‖ ^ (2 * N)) * ‖g x‖) := by ring
    _ ≤ 2 ^ N * ((1 + ‖x‖ ^ (2 * N)) * ‖g x‖) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 ^ N * (‖g x‖ + ‖x‖ ^ (2 * N) * ‖g x‖) := by ring
    _ ≤ 2 ^ N * ((SchwartzMap.seminorm ℂ 0 0) g + (SchwartzMap.seminorm ℂ (2 * N) 0) g) :=
        mul_le_mul_of_nonneg_left (add_le_add h2 h3) (by positivity)

/-- The first derivative seminorm controls the directional derivatives of `g` at every
sample point, with the polynomial weight `(k + 1) ^ N`, uniformly in the index. -/
lemma weight_mul_norm_fderiv_le_all {n : ℕ} [NeZero n] (N : ℕ) (k : ℕ) (g : 𝓢(E n, ℂ)) :
    ((k : ℝ) + 1) ^ N *
        ‖fderiv ℝ (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k : ℝ)))) (realIncl (n := n) 1)‖
      ≤ 2 ^ N * ((SchwartzMap.seminorm ℂ 0 1) g + (SchwartzMap.seminorm ℂ (2 * N) 1) g) := by
  set x : E n := realIncl (n := n) (Real.sqrt (2 * (k : ℝ))) with hx
  have hw := sample_weight_le_all (n := n) N k
  rw [← hx] at hw
  have hop : ‖fderiv ℝ (⇑g) x (realIncl (n := n) 1)‖ ≤ ‖fderiv ℝ (⇑g) x‖ := by
    calc _ ≤ ‖fderiv ℝ (⇑g) x‖ * ‖realIncl (n := n) 1‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (⇑g) x‖ := by rw [Work.Sampling.realIncl_norm_one, mul_one]
  have hmaxle : max 1 (‖x‖ ^ (2 * N)) ≤ 1 + ‖x‖ ^ (2 * N) := by
    refine max_le ?_ ?_
    · linarith [pow_nonneg (norm_nonneg x) (2 * N)]
    · linarith
  have h1 : max 1 (‖x‖ ^ (2 * N)) * ‖fderiv ℝ (⇑g) x (realIncl (n := n) 1)‖
      ≤ (1 + ‖x‖ ^ (2 * N)) * ‖fderiv ℝ (⇑g) x (realIncl (n := n) 1)‖ :=
    mul_le_mul_of_nonneg_right hmaxle (norm_nonneg _)
  have h2 : ‖fderiv ℝ (⇑g) x (realIncl (n := n) 1)‖ ≤ (SchwartzMap.seminorm ℂ 0 1) g := by
    refine le_trans hop ?_
    have := SchwartzMap.le_seminorm ℂ 0 1 g x
    rw [pow_zero, one_mul, norm_iteratedFDeriv_one] at this
    exact this
  have h3 : ‖x‖ ^ (2 * N) * ‖fderiv ℝ (⇑g) x (realIncl (n := n) 1)‖
      ≤ (SchwartzMap.seminorm ℂ (2 * N) 1) g := by
    have := SchwartzMap.le_seminorm ℂ (2 * N) 1 g x
    rw [norm_iteratedFDeriv_one] at this
    calc ‖x‖ ^ (2 * N) * ‖fderiv ℝ (⇑g) x (realIncl (n := n) 1)‖
        ≤ ‖x‖ ^ (2 * N) * ‖fderiv ℝ (⇑g) x‖ := mul_le_mul_of_nonneg_left hop (by positivity)
      _ ≤ _ := this
  calc ((k : ℝ) + 1) ^ N * ‖fderiv ℝ (⇑g) x (realIncl (n := n) 1)‖
      ≤ (2 ^ N * max 1 (‖x‖ ^ (2 * N))) * ‖fderiv ℝ (⇑g) x (realIncl (n := n) 1)‖ :=
        mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ = 2 ^ N * (max 1 (‖x‖ ^ (2 * N)) * ‖fderiv ℝ (⇑g) x (realIncl (n := n) 1)‖) := by ring
    _ ≤ 2 ^ N * ((1 + ‖x‖ ^ (2 * N)) * ‖fderiv ℝ (⇑g) x (realIncl (n := n) 1)‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 ^ N * (‖fderiv ℝ (⇑g) x (realIncl (n := n) 1)‖
          + ‖x‖ ^ (2 * N) * ‖fderiv ℝ (⇑g) x (realIncl (n := n) 1)‖) := by ring
    _ ≤ 2 ^ N * ((SchwartzMap.seminorm ℂ 0 1) g + (SchwartzMap.seminorm ℂ (2 * N) 1) g) :=
        mul_le_mul_of_nonneg_left (add_le_add h2 h3) (by positivity)

/-! ### Explicit forms of the four samples -/

lemma coeffs_apply_zero_gen {n : ℕ} [NeZero n] {k₀ : ℕ} (f : 𝓢(E n, ℂ)) (k : Set.Ici k₀) :
    coeffs n k₀ f (k, 0) = f (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ)))) := by
  simp [coeffs, Function.uncurry_apply_pair]

lemma coeffs_apply_one_gen {n : ℕ} [NeZero n] {k₀ : ℕ} (f : 𝓢(E n, ℂ)) (k : Set.Ici k₀) :
    coeffs n k₀ f (k, 1)
      = (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f)
          (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ)))) := by
  simp [coeffs, Function.uncurry_apply_pair]

lemma coeffs_apply_two_gen {n : ℕ} [NeZero n] {k₀ : ℕ} (f : 𝓢(E n, ℂ)) (k : Set.Ici k₀) :
    coeffs n k₀ f (k, 2)
      = fderiv ℝ (⇑f) (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ)))) (realIncl (n := n) 1) := by
  simp only [coeffs, Function.uncurry_apply_pair]
  exact Work.Sampling.deriv_comp_realIncl (SchwartzMap.hasFDerivAt f _)

lemma coeffs_apply_three_gen {n : ℕ} [NeZero n] {k₀ : ℕ} (f : 𝓢(E n, ℂ)) (k : Set.Ici k₀) :
    coeffs n k₀ f (k, 3)
      = fderiv ℝ (⇑(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f))
          (realIncl (n := n) (Real.sqrt (2 * (k.1 : ℝ)))) (realIncl (n := n) 1) := by
  simp only [coeffs, Function.uncurry_apply_pair]
  exact Work.Sampling.deriv_comp_realIncl (SchwartzMap.hasFDerivAt _ _)

/-! ### Slotwise bounds, uniform in the index -/

lemma slot_zero_le_all {n : ℕ} [NeZero n] (N : ℕ) (k₀ : ℕ) (f : 𝓢(E n, ℂ))
    (k : Set.Ici k₀) :
    ((k.1 : ℝ) + 1) ^ N * ‖coeffs n k₀ f (k, 0)‖
      ≤ 2 ^ N * ((SchwartzMap.seminorm ℂ 0 0) f + (SchwartzMap.seminorm ℂ (2 * N) 0) f) := by
  rw [coeffs_apply_zero_gen]
  exact weight_mul_norm_sample_le_all N k.1 f

lemma slot_one_le_all {n : ℕ} [NeZero n] (N : ℕ) (k₀ : ℕ) (f : 𝓢(E n, ℂ))
    (k : Set.Ici k₀) :
    ((k.1 : ℝ) + 1) ^ N * ‖coeffs n k₀ f (k, 1)‖
      ≤ 2 ^ N * ((SchwartzMap.seminorm ℂ 0 0) (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f)
          + (SchwartzMap.seminorm ℂ (2 * N) 0)
              (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f)) := by
  rw [coeffs_apply_one_gen]
  exact weight_mul_norm_sample_le_all N k.1 _

lemma slot_two_le_all {n : ℕ} [NeZero n] (N : ℕ) (k₀ : ℕ) (f : 𝓢(E n, ℂ))
    (k : Set.Ici k₀) :
    ((k.1 : ℝ) + 1) ^ N * ‖coeffs n k₀ f (k, 2)‖
      ≤ 2 ^ N * ((SchwartzMap.seminorm ℂ 0 1) f + (SchwartzMap.seminorm ℂ (2 * N) 1) f) := by
  rw [coeffs_apply_two_gen]
  exact weight_mul_norm_fderiv_le_all N k.1 f

lemma slot_three_le_all {n : ℕ} [NeZero n] (N : ℕ) (k₀ : ℕ) (f : 𝓢(E n, ℂ))
    (k : Set.Ici k₀) :
    ((k.1 : ℝ) + 1) ^ N * ‖coeffs n k₀ f (k, 3)‖
      ≤ 2 ^ N * ((SchwartzMap.seminorm ℂ 0 1) (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f)
          + (SchwartzMap.seminorm ℂ (2 * N) 1)
              (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f)) := by
  rw [coeffs_apply_three_gen]
  exact weight_mul_norm_fderiv_le_all N k.1 _

/-! ### Uniform polynomial decay of the samples -/

/-- **Polynomial decay of the CKMRV samples in the index, uniformly in finitely many
Schwartz seminorms.**  For every `N` and every starting index `k₀`, there are finitely
many Schwartz seminorms whose supremum controls `(k + 1) ^ N * ‖coeffs n k₀ f (k, j)‖`
for every Schwartz function `f` and every sample index `k ≥ k₀`. -/
theorem coeffs_seminorm_decay_family_gen (n : ℕ) [NeZero n] (k₀ N : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : 𝓢(E n, ℂ)) (i : SampleIdx k₀),
        ((i.1.1 : ℝ) + 1) ^ N * ‖coeffs n k₀ f i‖
          ≤ C * s.sup (schwartzSeminormFamily ℂ (E n) ℂ) f := by
  classical
  obtain ⟨s₀₀, C₀₀, hC₀₀, h₀₀⟩ := fourier_seminorm_le_family n 0 0
  obtain ⟨s₂₀, C₂₀, hC₂₀, h₂₀⟩ := fourier_seminorm_le_family n (2 * N) 0
  obtain ⟨s₀₁, C₀₁, hC₀₁, h₀₁⟩ := fourier_seminorm_le_family n 0 1
  obtain ⟨s₂₁, C₂₁, hC₂₁, h₂₁⟩ := fourier_seminorm_le_family n (2 * N) 1
  set S : Finset (ℕ × ℕ) :=
    ({(0, 0), (2 * N, 0), (0, 1), (2 * N, 1)} : Finset (ℕ × ℕ)) ∪ s₀₀ ∪ s₂₀ ∪ s₀₁ ∪ s₂₁
    with hS
  set D : ℝ := max 1 (max (max C₀₀ C₂₀) (max C₀₁ C₂₁)) with hD
  have hD1 : (1 : ℝ) ≤ D := by
    rw [hD]; exact le_max_left _ _
  have hDnn : 0 ≤ D := le_trans zero_le_one hD1
  have hD₀₀ : C₀₀ ≤ D := by
    rw [hD]
    exact le_trans (le_max_left C₀₀ C₂₀)
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have hD₂₀ : C₂₀ ≤ D := by
    rw [hD]
    exact le_trans (le_max_right C₀₀ C₂₀)
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have hD₀₁ : C₀₁ ≤ D := by
    rw [hD]
    exact le_trans (le_max_left C₀₁ C₂₁)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hD₂₁ : C₂₁ ≤ D := by
    rw [hD]
    exact le_trans (le_max_right C₀₁ C₂₁)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hA : ∀ m ∈ ({(0, 0), (2 * N, 0), (0, 1), (2 * N, 1)} : Finset (ℕ × ℕ)), m ∈ S := by
    intro m hm
    rw [hS]
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ hm)))
  have hs₀₀ : s₀₀ ⊆ S := by
    intro m hm; rw [hS]
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_right _ hm)))
  have hs₂₀ : s₂₀ ⊆ S := by
    intro m hm; rw [hS]
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ hm))
  have hs₀₁ : s₀₁ ⊆ S := by
    intro m hm; rw [hS]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hm)
  have hs₂₁ : s₂₁ ⊆ S := by
    intro m hm; rw [hS]
    exact Finset.mem_union_right _ hm
  refine ⟨S, 2 ^ (N + 1) * D, ?_, ?_⟩
  · positivity
  intro f i
  set Sf : ℝ := (S.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f with hSf
  have hSfnn : 0 ≤ Sf := by rw [hSf]; exact apply_nonneg _ _
  have hsub : ∀ s' : Finset (ℕ × ℕ), s' ⊆ S →
      (s'.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f ≤ Sf := by
    intro s' hs'
    rw [hSf]
    exact Seminorm.le_def.mp (Finset.sup_mono hs') f
  have hmem : ∀ m ∈ S, (schwartzSeminormFamily ℂ (E n) ℂ m) f ≤ D * Sf := by
    intro m hm
    have h1 : (schwartzSeminormFamily ℂ (E n) ℂ m) f ≤ Sf :=
      Seminorm.le_def.mp (Finset.le_sup hm) f
    calc (schwartzSeminormFamily ℂ (E n) ℂ m) f ≤ Sf := h1
      _ = 1 * Sf := (one_mul _).symm
      _ ≤ D * Sf := mul_le_mul_of_nonneg_right hD1 hSfnn
  have key : ∀ (s' : Finset (ℕ × ℕ)) (C' : ℝ), s' ⊆ S → C' ≤ D →
      C' * (s'.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f ≤ D * Sf := by
    intro s' C' hs' hC'
    exact mul_le_mul hC' (hsub s' hs') (apply_nonneg _ _) hDnn
  have hf00 : (SchwartzMap.seminorm ℂ 0 0) f ≤ D * Sf := by
    rw [← SchwartzMap.schwartzSeminormFamily_apply]
    exact hmem (0, 0) (hA _ (by simp))
  have hf20 : (SchwartzMap.seminorm ℂ (2 * N) 0) f ≤ D * Sf := by
    rw [← SchwartzMap.schwartzSeminormFamily_apply]
    exact hmem (2 * N, 0) (hA _ (by simp))
  have hf01 : (SchwartzMap.seminorm ℂ 0 1) f ≤ D * Sf := by
    rw [← SchwartzMap.schwartzSeminormFamily_apply]
    exact hmem (0, 1) (hA _ (by simp))
  have hf21 : (SchwartzMap.seminorm ℂ (2 * N) 1) f ≤ D * Sf := by
    rw [← SchwartzMap.schwartzSeminormFamily_apply]
    exact hmem (2 * N, 1) (hA _ (by simp))
  have hh00 : (SchwartzMap.seminorm ℂ 0 0) (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f)
      ≤ D * Sf := le_trans (h₀₀ f) (key s₀₀ C₀₀ hs₀₀ hD₀₀)
  have hh20 : (SchwartzMap.seminorm ℂ (2 * N) 0)
      (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f) ≤ D * Sf :=
    le_trans (h₂₀ f) (key s₂₀ C₂₀ hs₂₀ hD₂₀)
  have hh01 : (SchwartzMap.seminorm ℂ 0 1) (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f)
      ≤ D * Sf := le_trans (h₀₁ f) (key s₀₁ C₀₁ hs₀₁ hD₀₁)
  have hh21 : (SchwartzMap.seminorm ℂ (2 * N) 1)
      (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f) ≤ D * Sf :=
    le_trans (h₂₁ f) (key s₂₁ C₂₁ hs₂₁ hD₂₁)
  obtain ⟨k, j⟩ := i
  have hgoal : ((k.1 : ℝ) + 1) ^ N * ‖coeffs n k₀ f (k, j)‖ ≤ (2 ^ (N + 1) * D) * Sf := by
    fin_cases j
    · refine le_trans (slot_zero_le_all N k₀ f k) ?_
      calc 2 ^ N * ((SchwartzMap.seminorm ℂ 0 0) f + (SchwartzMap.seminorm ℂ (2 * N) 0) f)
          ≤ 2 ^ N * (D * Sf + D * Sf) :=
            mul_le_mul_of_nonneg_left (add_le_add hf00 hf20) (by positivity)
        _ = (2 ^ (N + 1) * D) * Sf := by rw [pow_succ]; ring
    · refine le_trans (slot_one_le_all N k₀ f k) ?_
      calc 2 ^ N * ((SchwartzMap.seminorm ℂ 0 0) (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f)
              + (SchwartzMap.seminorm ℂ (2 * N) 0)
                  (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f))
          ≤ 2 ^ N * (D * Sf + D * Sf) :=
            mul_le_mul_of_nonneg_left (add_le_add hh00 hh20) (by positivity)
        _ = (2 ^ (N + 1) * D) * Sf := by rw [pow_succ]; ring
    · refine le_trans (slot_two_le_all N k₀ f k) ?_
      calc 2 ^ N * ((SchwartzMap.seminorm ℂ 0 1) f + (SchwartzMap.seminorm ℂ (2 * N) 1) f)
          ≤ 2 ^ N * (D * Sf + D * Sf) :=
            mul_le_mul_of_nonneg_left (add_le_add hf01 hf21) (by positivity)
        _ = (2 ^ (N + 1) * D) * Sf := by rw [pow_succ]; ring
    · refine le_trans (slot_three_le_all N k₀ f k) ?_
      calc 2 ^ N * ((SchwartzMap.seminorm ℂ 0 1) (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f)
              + (SchwartzMap.seminorm ℂ (2 * N) 1)
                  (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f))
          ≤ 2 ^ N * (D * Sf + D * Sf) :=
            mul_le_mul_of_nonneg_left (add_le_add hh01 hh21) (by positivity)
        _ = (2 ^ (N + 1) * D) * Sf := by rw [pow_succ]; ring
  rw [hSf] at hgoal
  exact hgoal

/-- The weight `1 / (k + 1) ^ 2` is summable over the sample index, for every `k₀`. -/
lemma summable_sampleWeight_inv_sq_gen (k₀ : ℕ) :
    Summable (fun i : SampleIdx k₀ => 1 / (((i.1.1 : ℝ) + 1) ^ 2)) := by
  have hbase : Summable fun m : ℕ => 1 / (((m : ℝ) + 1) ^ 2) := by
    have h2 : Summable fun m : ℕ => 1 / ((m : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow).mpr (by norm_num)
    have h3 : Summable fun m : ℕ => 1 / (((m + 1 : ℕ) : ℝ) ^ 2) :=
      (summable_nat_add_iff (f := fun m : ℕ => 1 / ((m : ℝ) ^ 2)) 1).mpr h2
    simpa [Nat.cast_add, Nat.cast_one] using h3
  have hsub : Summable fun m : Set.Ici k₀ => 1 / (((m.1 : ℝ) + 1) ^ 2) :=
    hbase.subtype (fun m => k₀ ≤ m)
  refine (summable_prod_of_nonneg
    (f := fun p : SampleIdx k₀ => 1 / (((p.1.1 : ℝ) + 1) ^ 2)) (fun p => by positivity)).mpr
    ⟨fun _ => Summable.of_finite, ?_⟩
  have hconst : (fun x : Set.Ici k₀ => ∑' _y : Fin 4, 1 / (((x.1 : ℝ) + 1) ^ 2))
      = fun x : Set.Ici k₀ => 4 * (1 / (((x.1 : ℝ) + 1) ^ 2)) := by
    funext x
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  rw [hconst]
  exact hsub.mul_left 4

/-! ### The reconstruction series -/

/-- **The reconstruction series converges and is bounded by finitely many Schwartz
seminorms**, uniformly in the starting index. -/
theorem reconstruction_bound_gen {n : ℕ} [NeZero n] {k₀ : ℕ}
    (S : InterpolationSolutionGen n k₀) (x₀ : E n) :
    ∃ s : Finset (ℕ × ℕ), ∃ K : ℝ, 0 ≤ K ∧
      ∀ f : 𝓢(E n, ℂ),
        Summable (fun i : SampleIdx k₀ => coeffs n k₀ f i * (S.basis i).1 x₀) ∧
        ‖∑' i : SampleIdx k₀, coeffs n k₀ f i * (S.basis i).1 x₀‖
          ≤ K * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := by
  classical
  obtain ⟨Cb, Nb, hCb, hb⟩ := SeminormGrowthOfRadialGrowth S.basis S.growth_radial 0 0
  obtain ⟨s, Cc, hCc, hdecay⟩ := coeffs_seminorm_decay_family_gen n k₀ (Nb + 2)
  have hSigmann : 0 ≤ ∑' i : SampleIdx k₀, 1 / (((i.1.1 : ℝ) + 1) ^ 2) :=
    tsum_nonneg (fun i => by positivity)
  refine ⟨s, Cc * Cb * (∑' i : SampleIdx k₀, 1 / (((i.1.1 : ℝ) + 1) ^ 2)),
    mul_nonneg (mul_nonneg hCc hCb) hSigmann, fun f => ?_⟩
  set Sf : ℝ := (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f with hSf
  have hSf0 : 0 ≤ Sf := by rw [hSf]; exact apply_nonneg _ _
  have hbound : ∀ i : SampleIdx k₀,
      ‖coeffs n k₀ f i‖ * ‖(S.basis i).1 x₀‖
        ≤ (Cc * Cb * Sf) * (1 / (((i.1.1 : ℝ) + 1) ^ 2)) := by
    intro i
    set D : ℝ := (i.1.1 : ℝ) + 1 with hD
    have hDpos : 0 < D := by rw [hD]; positivity
    have hDpow : 0 < D ^ Nb := pow_pos hDpos _
    have h1 : D ^ (Nb + 2) * ‖coeffs n k₀ f i‖ ≤ Cc * Sf := by
      rw [hD, hSf]; exact hdecay f i
    have h2 : ‖(S.basis i).1 x₀‖ ≤ Cb * D ^ Nb := by
      refine le_trans (SchwartzMap.norm_le_seminorm ℂ (S.basis i).1 x₀) ?_
      rw [hD]
      exact hb i.1 i.2
    have h3 : D ^ (Nb + 2) * (‖coeffs n k₀ f i‖ * ‖(S.basis i).1 x₀‖)
        ≤ (Cc * Sf) * (Cb * D ^ Nb) := by
      calc D ^ (Nb + 2) * (‖coeffs n k₀ f i‖ * ‖(S.basis i).1 x₀‖)
          = (D ^ (Nb + 2) * ‖coeffs n k₀ f i‖) * ‖(S.basis i).1 x₀‖ := by ring
        _ ≤ (Cc * Sf) * ‖(S.basis i).1 x₀‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ (Cc * Sf) * (Cb * D ^ Nb) := mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : D ^ Nb * (D ^ 2 * (‖coeffs n k₀ f i‖ * ‖(S.basis i).1 x₀‖))
        ≤ D ^ Nb * (Cc * Cb * Sf) := by
      calc D ^ Nb * (D ^ 2 * (‖coeffs n k₀ f i‖ * ‖(S.basis i).1 x₀‖))
          = D ^ (Nb + 2) * (‖coeffs n k₀ f i‖ * ‖(S.basis i).1 x₀‖) := by
            rw [pow_add]; ring
        _ ≤ (Cc * Sf) * (Cb * D ^ Nb) := h3
        _ = D ^ Nb * (Cc * Cb * Sf) := by ring
    have h5 : D ^ 2 * (‖coeffs n k₀ f i‖ * ‖(S.basis i).1 x₀‖) ≤ Cc * Cb * Sf :=
      (mul_le_mul_iff_of_pos_left hDpow).mp h4
    have h6 : ‖coeffs n k₀ f i‖ * ‖(S.basis i).1 x₀‖ ≤ (Cc * Cb * Sf) * (1 / D ^ 2) := by
      rw [mul_one_div, le_div_iff₀ (by positivity : (0 : ℝ) < D ^ 2)]
      calc (‖coeffs n k₀ f i‖ * ‖(S.basis i).1 x₀‖) * D ^ 2
          = D ^ 2 * (‖coeffs n k₀ f i‖ * ‖(S.basis i).1 x₀‖) := by ring
        _ ≤ Cc * Cb * Sf := h5
    rwa [hD] at h6
  have hsum_norm : Summable (fun i : SampleIdx k₀ => ‖coeffs n k₀ f i‖ * ‖(S.basis i).1 x₀‖) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hbound
      ((summable_sampleWeight_inv_sq_gen k₀).mul_left (Cc * Cb * Sf))
  have hsum_f : Summable (fun i : SampleIdx k₀ => coeffs n k₀ f i * (S.basis i).1 x₀) :=
    Summable.of_norm_bounded hsum_norm (fun i => le_of_eq (norm_mul _ _))
  refine ⟨hsum_f, ?_⟩
  calc ‖∑' i : SampleIdx k₀, coeffs n k₀ f i * (S.basis i).1 x₀‖
      ≤ ∑' i : SampleIdx k₀, ‖coeffs n k₀ f i * (S.basis i).1 x₀‖ :=
        norm_tsum_le_tsum_norm hsum_f.norm
    _ = ∑' i : SampleIdx k₀, ‖coeffs n k₀ f i‖ * ‖(S.basis i).1 x₀‖ :=
        tsum_congr (fun i => norm_mul _ _)
    _ ≤ ∑' i : SampleIdx k₀, (Cc * Cb * Sf) * (1 / (((i.1.1 : ℝ) + 1) ^ 2)) :=
        Summable.tsum_le_tsum hbound hsum_norm
          ((summable_sampleWeight_inv_sq_gen k₀).mul_left (Cc * Cb * Sf))
    _ = (Cc * Cb * Sf) * ∑' i : SampleIdx k₀, 1 / (((i.1.1 : ℝ) + 1) ^ 2) := tsum_mul_left
    _ = (Cc * Cb * (∑' i : SampleIdx k₀, 1 / (((i.1.1 : ℝ) + 1) ^ 2)))
          * (s.sup (schwartzSeminormFamily ℂ (E n) ℂ)) f := by rw [hSf]; ring

theorem ReconstructionCLMGen {n : ℕ} [NeZero n] {k₀ : ℕ} (S : InterpolationSolutionGen n k₀)
    (x₀ : E n) :
    ∃ Λ : 𝓢(E n, ℂ) →L[ℂ] ℂ, ∀ f : 𝓢(E n, ℂ),
      Λ f = (∑' i : SampleIdx k₀, coeffs n k₀ f i * (S.basis i).1 x₀) - f x₀ := by
  classical
  obtain ⟨C, hC⟩ := Work.Sampling.coeffs_continuous_linear n k₀
  obtain ⟨s, K, hK, hb⟩ := reconstruction_bound_gen S x₀
  have hcoeffs_add : ∀ f g : 𝓢(E n, ℂ),
      coeffs n k₀ (f + g) = coeffs n k₀ f + coeffs n k₀ g := by
    intro f g; rw [← hC (f + g), ← hC f, ← hC g, map_add]
  have hcoeffs_smul : ∀ (a : ℂ) (f : 𝓢(E n, ℂ)),
      coeffs n k₀ (a • f) = a • coeffs n k₀ f := by
    intro a f; rw [← hC (a • f), ← hC f, map_smul]
  have hadd : ∀ f g : 𝓢(E n, ℂ),
      (∑' i : SampleIdx k₀, coeffs n k₀ (f + g) i * (S.basis i).1 x₀)
        = (∑' i : SampleIdx k₀, coeffs n k₀ f i * (S.basis i).1 x₀)
          + (∑' i : SampleIdx k₀, coeffs n k₀ g i * (S.basis i).1 x₀) := by
    intro f g
    rw [hcoeffs_add f g]
    simp only [Pi.add_apply, add_mul]
    exact Summable.tsum_add (hb f).1 (hb g).1
  have hsmul : ∀ (a : ℂ) (f : 𝓢(E n, ℂ)),
      (∑' i : SampleIdx k₀, coeffs n k₀ (a • f) i * (S.basis i).1 x₀)
        = a • (∑' i : SampleIdx k₀, coeffs n k₀ f i * (S.basis i).1 x₀) := by
    intro a f
    have hcf : ∀ i, coeffs n k₀ (a • f) i = a * coeffs n k₀ f i := by
      intro i
      simpa [Pi.smul_apply, smul_eq_mul] using congrFun (hcoeffs_smul a f) i
    simp only [hcf, mul_assoc]
    rw [tsum_mul_left, smul_eq_mul]
  have hbnd : ∃ s' : Finset (ℕ × ℕ), ∃ C' : ℝ, 0 ≤ C' ∧ ∀ f : 𝓢(E n, ℂ),
      ‖∑' i : SampleIdx k₀, coeffs n k₀ f i * (S.basis i).1 x₀‖
        ≤ C' * s'.sup (schwartzSeminormFamily ℂ (E n) ℂ) f :=
    ⟨s, K, hK, fun f => (hb f).2⟩
  let A : 𝓢(E n, ℂ) →L[ℂ] ℂ :=
    SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ) (𝕜' := ℂ) (D := E n) (E := ℂ) (G := ℂ)
      (σ := RingHom.id ℂ)
      (fun f => ∑' i : SampleIdx k₀, coeffs n k₀ f i * (S.basis i).1 x₀) hadd hsmul hbnd
  refine ⟨A - Work.Sampling.evalAtCLM x₀, fun f => ?_⟩
  rw [sub_apply, Work.Sampling.evalAtCLM_apply]
  rfl

end

end Work.FunctionalEquations
