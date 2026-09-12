import Mathlib
import Submission.LMProbs
import Submission.LMMeas
import Submission.F_gauss

/-!
Moment growth of the Lovett--Meka walk (child task).

TASK: prove `exp_norm_sq_lower` below.  You may add any
helper definitions/lemmas above it in this file.

Meaning (real integrals, `mu n T` is a probability measure on
`Omega n T = Fin T → Vec n`, `Vec n = EuclideanSpace ℝ (Fin n)`, `mu` is the
product of `T` standard Gaussians):

  E‖X_T - x0‖² ≥ γ² · T · (n − E|A_T| − E|B_T|)

where X_t = Xn n T δ γ x0 v c ω t is the walk and
  A_T = frozenVars δ (X_T)    (subset of Fin n),
  B_T = frozenRows δ x0 v c (X_T)   (subset of ι),
counted in ℝ.

PROOF SKETCH.

Write U_s := Proj n T δ γ x0 v c ω s = walkProj v (A_s) (B_s) (oracle ω s), where
A_s := frozenVars δ (Xn n T δ γ x0 v c ω s), B_s := frozenRows ... (Xn ... s).
By telescoping (`Xn_telescope`) X_T − x0 = γ • Σ_{s < T} U_s.

Claim 1 (orthogonality of steps, cross terms vanish).  For s < T,
`E⟨X_s − x0, U_s⟩ = 0` because given the first s coordinates (which determine
X_s and the projection matrix) the fresh Gaussian `ω s` has mean 0.  More
generally for s < t: `E⟨U_s, U_t⟩ = 0`.  Concretely: `U_t` is (given the past)
`Proj g` with `g = ω t` a standard Gaussian, so its conditional expectation is
0; `U_s` and `X_s − x0` depend only on coordinates `< s` (and `≤ t`).

Hence
  E‖X_T − x0‖² = γ² · Σ_{s < T} E‖U_s‖²                     (use Xn_telescope,
    expand the squared norm of a sum, cross terms are 0).

Claim 2 (per-step variance equals the free dimension).  For FIXED finite
`A : Finset (Fin n)`, `B : Finset ι` and `g` a standard Gaussian on `Vec n`:

  ∫ g, ‖walkProj v A B g‖² = finrank ℝ (Wspan v A B)ᗮ

(standard Gaussian on a subspace has squared norm expectation = the dimension;
`walkProj v A B g = ((Wspan v A B)ᗮ).starProjection g`, see `Submission.LMWalk`).
Also  finrank ℝ (Wspan v A B)ᗮ ≥ n − |A| − |B|  because
finrank (Wspan v A B) ≤ |A| + |B| (span of ≤ |A|+|B| generators) and
`finrank_add_finrank_orthogonal` (in
`Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`):
finrank K + finrank Kᗮ = finrank ℝ (Vec n) = n.  Useful: norm_sq_sum,
`LinearMap.trace` (if used), `OrthonormalBasis`, `EuclideanSpace.real_norm_sq_eq`.

Suggested route for Claim 2 (choose your own):
- E‖Proj g‖² = finrank Wᗮ.  Pick an orthonormal basis {u_l} of Wᗮ
  (mathlib has orthonormal bases for finite-dimensional subspaces / use
  `exists_orthonormalBasis` or Gram–Schmidt results); ‖Proj g‖² = Σ_l ⟪g,u_l⟫²;
  then E⟪g,u⟫² = ‖u‖² for each fixed u (coordinate computation using the
  definition of `stdGaussian (Vec n)` as the law of a vector of n independent
  standard normals, or via `gauss_mgf`/`gaussian_mgf_one` from
  `Submission.F_gauss`; E x² = 1 and E x = 0 for `gaussianReal 0 1`).

Claim 3 (freeze sets grow).  A_s ⊆ A_T and B_s ⊆ B_T for s ≤ T
(`frozenVars_subset_of_le`, `frozenRows_subset_of_le` in `Submission.LMWalk`
apply to the xseq trajectory `Xn n T ... ω t`).  Hence
|A_s| ≤ |A_T|, |B_s| ≤ |B_T|, so pointwise
n − |A_s| − |B_s| ≥ n − |A_T| − |B_T|.

Claims 2+3 give, for each s < T,
  E‖U_s‖² ≥ E[n − |A_T| − |B_T|]       (condition on the first s coordinates;
    the inner integral over the fresh Gaussian is ≥ finrank Wᗮ ≥ n−|A_s|−|B_s|
    ≥ n − |A_T| − |B_T|).

Sum over s < T:  E‖X_T − x0‖² ≥ γ²·T·(n − E|A_T| − E|B_T|).

MEASURE-THEORETIC NOTES:
- `∫` is the real (Bochner) integral; `mu n T` is a probability measure.
- Functions of the first k coordinates integrate the same over `mu n T` and
  `mu n k` (prove a real-integral analogue of `lintegral_first` from
  `Submission.LMProbs` if you need it: map via
  `(mu n T).map (first T k ht)` and use `MeasureTheory.integral_map` with a
  measure-preserving/prod structure, or argue with `peelEquiv` + `mu` being a
  product; the remaining T−k Gaussians integrate to 1).
- To split off the fresh coordinate s: use the measurable equivalence
  `peelEquiv n s : Omega n (s+1) ≃ᵐ (Vec n × Omega n s)` (see LMProbs) or
  `MeasureTheory.lintegral_snoc_form`/Fubini; note `mu n T` restricted to the
  first s+1 coordinates is `mu n (s+1)` (product measure).
- All integrands are continuous/bounded where needed; polynomial growth in the
  Gaussians guarantees integrability (‖Xn t‖ grows at most linearly in the
  Gaussian norms).
- Real integrals of non-negative functions are safe once you prove
  integrability (e.g. by explicit pointwise bounds); don't rely on real
  integrals of possibly-nonintegrable functions.

FINISHING: state the RHS exactly as in the theorem (the integrands for |A_T|
and |B_T| are `(Finset.card ... : ℝ)` over `ω`), then convert everything into
one real inequality.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory

noncomputable section
open Classical

namespace Submission.Discrepancy


/-! ### Part I: finite-dimensional Gaussian facts (Claim 2) -/

/-- Second moment of a linear functional of the standard Gaussian: E⟨g,u⟩² = ‖u‖². -/
lemma gauss_sq_lin (n : ℕ) (u : Vec n) :
    (∫ g : Vec n, (vin g u) ^ 2 ∂(stdGaussian (Vec n))) = ‖u‖ ^ 2 := by
  have hmem : MemLp id 2 (stdGaussian (Vec n)) :=
    ProbabilityTheory.IsGaussian.memLp_two_id (μ := stdGaussian (Vec n))
  have hcov := ProbabilityTheory.covarianceBilin_apply (μ := stdGaussian (Vec n)) hmem u u
  have hid0 : (stdGaussian (Vec n))[id] = 0 := by
    simpa using (ProbabilityTheory.integral_id_stdGaussian (E := Vec n))
  have hmain : (∫ g : Vec n, (vin g u) ^ 2 ∂(stdGaussian (Vec n))) =
      covarianceBilin (stdGaussian (Vec n)) u u := by
    rw [hcov, hid0]
    congr 1
    funext g
    simp [vin, pow_two, real_inner_comm]
  rw [hmain]
  rw [ProbabilityTheory.covarianceBilin_stdGaussian (E := Vec n)]
  rw [innerSL_apply_apply]
  exact inner_self_eq_norm_sq (𝕜 := ℝ) (x := u)

/-- ‖g‖² is integrable under the standard Gaussian. -/
lemma integrable_norm_sq_gauss (n : ℕ) :
    Integrable (fun g : Vec n => ‖g‖ ^ 2) (stdGaussian (Vec n)) := by
  have hm : MemLp id 2 (stdGaussian (Vec n)) :=
    ProbabilityTheory.IsGaussian.memLp_two_id (μ := stdGaussian (Vec n))
  exact (memLp_two_iff_integrable_sq_norm (f := id) (μ := stdGaussian (Vec n)) hm.aestronglyMeasurable).1 hm

/-- ⟨g,u⟩² is integrable under the standard Gaussian. -/
lemma integrable_sq_lin (n : ℕ) (u : Vec n) :
    Integrable (fun g : Vec n => (vin g u) ^ 2) (stdGaussian (Vec n)) := by
  have hm : Measurable (fun g : Vec n => vin g u) := measurable_vin n u
  have hf : AEStronglyMeasurable (fun g : Vec n => (vin g u) ^ 2) (stdGaussian (Vec n)) :=
    (hm.pow_const 2).aestronglyMeasurable
  have hg : Integrable (fun g : Vec n => ‖u‖ ^ 2 * ‖g‖ ^ 2) (stdGaussian (Vec n)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (integrable_norm_sq_gauss n).const_mul (‖u‖ ^ 2)
  refine Integrable.mono' hg hf ?_
  filter_upwards with g
  have hb : |vin g u| ≤ ‖g‖ * ‖u‖ := by
    simpa [vin] using (abs_real_inner_le_norm g u)
  calc
    ‖(vin g u) ^ 2‖ = (vin g u) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    _ = |vin g u| ^ 2 := by rw [sq_abs]
    _ ≤ (‖g‖ * ‖u‖) ^ 2 := by
          apply sq_le_sq.mpr
          simpa [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using hb
    _ = ‖u‖ ^ 2 * ‖g‖ ^ 2 := by ring

/-- Projection fixes points of its subspace. -/
lemma starProjection_of_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] (v : E) (hv : v ∈ K) :
    K.starProjection v = v := by
  exact Submodule.eq_starProjection_of_mem_orthogonal (K := K) (u := v) (v := v) hv (by simp)

/-- Expected squared norm of the projected Gaussian equals the free dimension. -/
lemma gauss_sq_proj {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n) (A : Finset (Fin n))
    (B : Finset ι) :
    (∫ g : Vec n, ‖walkProj v A B g‖ ^ 2 ∂(stdGaussian (Vec n))) =
      (Module.finrank ℝ (Wspan v A B)ᗮ : ℝ) := by
  let K : Submodule ℝ (Vec n) := (Wspan v A B)ᗮ
  let S := ↥K
  let b : OrthonormalBasis (Fin (Module.finrank ℝ S)) ℝ S := stdOrthonormalBasis ℝ S
  have hsq (g : Vec n) : ‖walkProj v A B g‖ ^ 2 =
      ∑ i : Fin (Module.finrank ℝ S), (inner ℝ g ((b i : S) : Vec n)) ^ 2 := by
    have hmem : K.starProjection g ∈ K := Submodule.starProjection_apply_mem (U := K) g
    calc
      ‖walkProj v A B g‖ ^ 2 = ‖K.starProjection g‖ ^ 2 := rfl
      _ = ‖(⟨K.starProjection g, hmem⟩ : S)‖ ^ 2 := by rfl
      _ = ∑ i : Fin (Module.finrank ℝ S),
            (inner ℝ (⟨K.starProjection g, hmem⟩ : S) (b i)) ^ 2 := by
            exact (OrthonormalBasis.sum_sq_inner_left b (⟨K.starProjection g, hmem⟩ : S)).symm
      _ = ∑ i : Fin (Module.finrank ℝ S),
            (inner ℝ (K.starProjection g) ((b i : S) : Vec n)) ^ 2 := by
            congr 1
      _ = ∑ i : Fin (Module.finrank ℝ S), (inner ℝ g ((b i : S) : Vec n)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            have h2 : inner ℝ (K.starProjection g) ((b i : S) : Vec n) =
                inner ℝ g (K.starProjection ((b i : S) : Vec n)) := by
              exact Submodule.inner_starProjection_left_eq_right (𝕜 := ℝ) (K := K) g ((b i : S) : Vec n)
            have h3 : K.starProjection ((b i : S) : Vec n) = ((b i : S) : Vec n) := by
              exact starProjection_of_mem K ((b i : S) : Vec n) (b i).2
            rw [h2, h3]
  calc
    (∫ g : Vec n, ‖walkProj v A B g‖ ^ 2 ∂(stdGaussian (Vec n)))
        = ∫ g : Vec n,
            (∑ i : Fin (Module.finrank ℝ S), (inner ℝ g ((b i : S) : Vec n)) ^ 2)
            ∂(stdGaussian (Vec n)) := by
            apply integral_congr_ae
            filter_upwards with g
            exact hsq g
    _ = ∑ i : Fin (Module.finrank ℝ S),
          (∫ g : Vec n, (inner ℝ g ((b i : S) : Vec n)) ^ 2 ∂(stdGaussian (Vec n))) := by
          rw [integral_finsetSum]
          intro i hi
          simpa [vin] using (integrable_sq_lin n ((b i : S) : Vec n))
    _ = (Module.finrank ℝ S : ℝ) := by
          calc
            (∑ i : Fin (Module.finrank ℝ S),
                (∫ g : Vec n, (inner ℝ g ((b i : S) : Vec n)) ^ 2 ∂(stdGaussian (Vec n))))
              = ∑ i : Fin (Module.finrank ℝ S), (1 : ℝ) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  have hlin := gauss_sq_lin n ((b i : S) : Vec n)
                  have hval : (∫ g : Vec n, (inner ℝ g ((b i : S) : Vec n)) ^ 2
                      ∂(stdGaussian (Vec n))) = 1 := by
                    have hb1 : ‖b i‖ = 1 := b.orthonormal.1 i
                    calc
                      (∫ g : Vec n, (inner ℝ g ((b i : S) : Vec n)) ^ 2 ∂(stdGaussian (Vec n)))
                          = (∫ g : Vec n, (vin g ((b i : S) : Vec n)) ^ 2 ∂(stdGaussian (Vec n))) := by
                            apply integral_congr_ae
                            filter_upwards with g
                            simp [vin]
                      _ = ‖((b i : S) : Vec n)‖ ^ 2 := gauss_sq_lin n ((b i : S) : Vec n)
                      _ = 1 := by
                            change ‖(b i : S)‖ ^ 2 = 1
                            rw [hb1]
                            norm_num
                  exact hval
            _ = (Module.finrank ℝ S : ℝ) := by simp
    _ = (Module.finrank ℝ (Wspan v A B)ᗮ : ℝ) := by rfl

/-- finrank of the frozen span is at most |A|+|B|. -/
lemma finrank_Wspan_le {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n) (A : Finset (Fin n))
    (B : Finset ι) :
    Module.finrank ℝ (Wspan v A B) ≤ A.card + B.card := by
  let SS : Finset (Vec n) := A.image (fun i : Fin n => basis n i) ∪ B.image v
  have hS : ((Wspan v A B : Submodule ℝ (Vec n)) = Submodule.span ℝ (SS : Set (Vec n))) := by
    unfold Wspan
    congr 1
    ext z
    simp [SS]
  rw [hS]
  have h1 : Module.finrank ℝ (Submodule.span ℝ (SS : Set (Vec n))) ≤ SS.card := by
    simpa using (finrank_span_le_card (R := ℝ) (M := Vec n) (SS : Set (Vec n)))
  have h2 : SS.card ≤ A.card + B.card := by
    exact (Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le Finset.card_image_le)
  exact h1.trans h2

/-- Dimension of the free subspace ≥ n − |A| − |B|. -/
lemma finrank_free_ge {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n) (A : Finset (Fin n))
    (B : Finset ι) :
    (n : ℝ) - (A.card : ℝ) - (B.card : ℝ) ≤ (Module.finrank ℝ (Wspan v A B)ᗮ : ℝ) := by
  have hdim := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := Vec n) (Wspan v A B)
  have hle := finrank_Wspan_le v A B
  have hdimR : (Module.finrank ℝ (Wspan v A B)ᗮ : ℝ) =
      (n : ℝ) - (Module.finrank ℝ (Wspan v A B) : ℝ) := by
    have hcast : (Module.finrank ℝ (Wspan v A B) : ℝ) + (Module.finrank ℝ (Wspan v A B)ᗮ : ℝ) = (n : ℝ) := by
      rw [← Nat.cast_add, hdim, finrank_euclidean]
    linarith
  rw [hdimR]
  have hleR : (Module.finrank ℝ (Wspan v A B) : ℝ) ≤ (A.card + B.card : ℝ) := by
    exact_mod_cast hle
  linarith

/-- Per-step Gaussian inequality (Claim 2): E‖Pg‖² ≥ n − |A| − |B|. -/
lemma gauss_proj_ge {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n) (A : Finset (Fin n))
    (B : Finset ι) :
    (n : ℝ) - (A.card : ℝ) - (B.card : ℝ) ≤
      (∫ g : Vec n, ‖walkProj v A B g‖ ^ 2 ∂(stdGaussian (Vec n))) := by
  rw [gauss_sq_proj v A B]
  exact finrank_free_ge v A B




/-- Mean of a linear functional of the standard Gaussian is zero. -/
lemma gauss_mean_lin (n : ℕ) (u : Vec n) :
    (∫ g : Vec n, vin g u ∂(stdGaussian (Vec n))) = 0 := by
  have hf : (fun g : Vec n => vin g u) = fun g => ((innerSL ℝ (E := Vec n)) u) g := by
    funext g
    simp [vin, real_inner_comm, innerSL_apply_apply]
  rw [hf]
  exact ProbabilityTheory.integral_strongDual_stdGaussian (E := Vec n)
    (L := (innerSL ℝ (E := Vec n)) u)

/-- ‖g‖ is integrable under the standard Gaussian. -/
lemma integrable_norm_gauss (n : ℕ) :
    Integrable (fun g : Vec n => ‖g‖) (stdGaussian (Vec n)) := by
  have hf : AEStronglyMeasurable (fun g : Vec n => ‖g‖) (stdGaussian (Vec n)) := by
    exact (measurable_norm n).aestronglyMeasurable
  have hconst : Integrable (fun _ : Vec n => (1 : ℝ)) (stdGaussian (Vec n)) := by
    simpa using (integrable_const (c := (1 : ℝ)) (μ := stdGaussian (Vec n)))
  have hb : Integrable (fun g : Vec n => (1 : ℝ) + ‖g‖ ^ 2) (stdGaussian (Vec n)) := by
    exact hconst.add (integrable_norm_sq_gauss n)
  refine Integrable.mono' hb hf ?_
  filter_upwards with g
  calc
    ‖‖g‖‖ = ‖g‖ := abs_of_nonneg (norm_nonneg g)
    _ ≤ (1 : ℝ) + ‖g‖ ^ 2 := by
          nlinarith [sq_nonneg ‖g‖]

/-- Cross term in one Gaussian step vanishes: E⟨a, Pg⟩ = 0. -/
lemma gauss_cross {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n) (A : Finset (Fin n))
    (B : Finset ι) (a : Vec n) :
    (∫ g : Vec n, (inner ℝ a (walkProj v A B g)) ∂(stdGaussian (Vec n))) = 0 := by
  have hpoint (g : Vec n) : (inner ℝ a (walkProj v A B g)) = vin g (walkProj v A B a) := by
    calc
      (inner ℝ a (walkProj v A B g)) = vin (walkProj v A B g) a := by
        simp [vin, real_inner_comm]
      _ = vin g (walkProj v A B a) := proj_adjoint v A B g a
  calc
    (∫ g : Vec n, (inner ℝ a (walkProj v A B g)) ∂(stdGaussian (Vec n)))
        = (∫ g : Vec n, vin g (walkProj v A B a) ∂(stdGaussian (Vec n))) := by
            apply integral_congr_ae
            filter_upwards with g
            exact hpoint g
    _ = 0 := gauss_mean_lin n (walkProj v A B a)

/-- ‖Pg‖² is integrable under the standard Gaussian. -/
lemma integrable_proj_sq {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n) (A : Finset (Fin n))
    (B : Finset ι) :
    Integrable (fun g : Vec n => ‖walkProj v A B g‖ ^ 2) (stdGaussian (Vec n)) := by
  have hc : Continuous (fun g : Vec n => ‖walkProj v A B g‖) := (continuous_walkProj v A B).norm
  have hf : AEStronglyMeasurable (fun g : Vec n => ‖walkProj v A B g‖ ^ 2)
      (stdGaussian (Vec n)) := by
    exact (hc.measurable.pow_const 2).aestronglyMeasurable
  refine Integrable.mono' (integrable_norm_sq_gauss n) hf ?_
  filter_upwards with g
  calc
    ‖‖walkProj v A B g‖ ^ 2‖ = ‖walkProj v A B g‖ ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    _ ≤ ‖g‖ ^ 2 := by
          apply sq_le_sq.mpr
          rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
          exact proj_norm_le v A B g

/-- Integrability of the linear term ⟨a, Pg⟩ under the standard Gaussian. -/
lemma integrable_lin_proj {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n) (A : Finset (Fin n))
    (B : Finset ι) (a : Vec n) :
    Integrable (fun g : Vec n => (inner ℝ a (walkProj v A B g))) (stdGaussian (Vec n)) := by
  have hcP : Continuous (fun g : Vec n => walkProj v A B g) := continuous_walkProj v A B
  have hc : Continuous (fun g : Vec n => (inner ℝ a (walkProj v A B g))) := by
    change Continuous ((fun p : Vec n × Vec n => ⟪p.1, p.2⟫) ∘ (fun g : Vec n => (a, walkProj v A B g)))
    exact continuous_inner.comp (Continuous.prodMk continuous_const hcP)
  have hf : AEStronglyMeasurable (fun g : Vec n => (inner ℝ a (walkProj v A B g)))
      (stdGaussian (Vec n)) := hc.measurable.aestronglyMeasurable
  have hbnd : Integrable (fun g : Vec n => ‖a‖ * ‖g‖) (stdGaussian (Vec n)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (integrable_norm_gauss n).const_mul ‖a‖
  refine Integrable.mono' hbnd hf ?_
  filter_upwards with g
  calc
    ‖(inner ℝ a (walkProj v A B g))‖ = |(inner ℝ a (walkProj v A B g))| := by
      rw [Real.norm_eq_abs]
    _ ≤ ‖a‖ * ‖walkProj v A B g‖ := by
      simpa using (abs_real_inner_le_norm a (walkProj v A B g))
    _ ≤ ‖a‖ * ‖g‖ := by
      exact mul_le_mul_of_nonneg_left (proj_norm_le v A B g) (norm_nonneg a)

/-- ‖x + γy‖² expansion. -/
lemma norm_sq_add_smul (n : ℕ) (a b : Vec n) (γ : ℝ) :
    ‖a + γ • b‖ ^ 2 = ‖a‖ ^ 2 + γ ^ 2 * ‖b‖ ^ 2 + 2 * γ * (inner ℝ a b) := by
  rw [norm_add_sq_real a (γ • b)]
  rw [show inner ℝ a (γ • b) = γ * inner ℝ a b by exact real_inner_smul_right a b γ]
  have hγ : ‖(γ : ℝ)‖ ^ 2 = γ ^ 2 := by simp
  rw [show ‖γ • b‖ ^ 2 = γ ^ 2 * ‖b‖ ^ 2 by
    rw [norm_smul]
    rw [show (‖γ‖ * ‖b‖) ^ 2 = ‖γ‖ ^ 2 * ‖b‖ ^ 2 by ring]
    rw [hγ]]
  ring

/-- Shifted projected step: expectation of squared norm (exact two-term identity). -/
lemma gauss_shift_norm_sq_eq {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n)
    (A : Finset (Fin n)) (B : Finset ι) (γ : ℝ) (a : Vec n) :
    (∫ g : Vec n, ‖a + γ • walkProj v A B g‖ ^ 2 ∂(stdGaussian (Vec n))) =
      ‖a‖ ^ 2 + γ ^ 2 *
        (∫ g : Vec n, ‖walkProj v A B g‖ ^ 2 ∂(stdGaussian (Vec n))) := by
  let F1 : Vec n → ℝ := fun _ => ‖a‖ ^ 2
  let F2 : Vec n → ℝ := fun g => γ ^ 2 * ‖walkProj v A B g‖ ^ 2
  let F3 : Vec n → ℝ := fun g => 2 * γ * (inner ℝ a (walkProj v A B g))
  have hfunc : (fun g : Vec n => ‖a + γ • walkProj v A B g‖ ^ 2) = fun g : Vec n =>
      F1 g + F2 g + F3 g := by
    funext g
    change ‖a + γ • walkProj v A B g‖ ^ 2 = ‖a‖ ^ 2 + γ ^ 2 * ‖walkProj v A B g‖ ^ 2
      + 2 * γ * (inner ℝ a (walkProj v A B g))
    exact norm_sq_add_smul n a (walkProj v A B g) γ
  rw [hfunc]
  have hi1 : Integrable F1 (stdGaussian (Vec n)) := by
    simpa [F1] using (integrable_const (c := ‖a‖ ^ 2) (μ := stdGaussian (Vec n)))
  have hi2 : Integrable F2 (stdGaussian (Vec n)) := by
    simpa [F2, mul_comm, mul_left_comm, mul_assoc] using
      (integrable_proj_sq v A B).const_mul (γ ^ 2)
  have hi3 : Integrable F3 (stdGaussian (Vec n)) := by
    simpa [F3, mul_assoc] using (integrable_lin_proj v A B a).const_mul (2 * γ)
  calc
    (∫ g : Vec n, F1 g + F2 g + F3 g ∂(stdGaussian (Vec n)))
        = ∫ g : Vec n, (F1 + F2 + F3) g ∂(stdGaussian (Vec n)) := rfl
    _ = (∫ g : Vec n, (F1 + F2) g ∂(stdGaussian (Vec n)))
          + (∫ g : Vec n, F3 g ∂(stdGaussian (Vec n))) := by
          exact integral_add (hi1.add hi2) hi3
    _ = (∫ g : Vec n, F1 g ∂(stdGaussian (Vec n))) + (∫ g : Vec n, F2 g ∂(stdGaussian (Vec n)))
          + (∫ g : Vec n, F3 g ∂(stdGaussian (Vec n))) := by
          congr 1
          exact integral_add hi1 hi2
    _ = ‖a‖ ^ 2 + γ ^ 2 * (∫ g : Vec n, ‖walkProj v A B g‖ ^ 2 ∂(stdGaussian (Vec n))) := by
          have hc1 : (∫ g : Vec n, F1 g ∂(stdGaussian (Vec n))) = ‖a‖ ^ 2 := by
            simp [F1]
          have hc2 : (∫ g : Vec n, F2 g ∂(stdGaussian (Vec n))) =
              γ ^ 2 * (∫ g : Vec n, ‖walkProj v A B g‖ ^ 2 ∂(stdGaussian (Vec n))) := by
            simp [F2]
            rw [integral_const_mul]
          have hc3 : (∫ g : Vec n, F3 g ∂(stdGaussian (Vec n))) = 0 := by
            have hcross := gauss_cross v A B a
            simp [F3]
            rw [integral_const_mul]
            rw [hcross]
            ring
          rw [hc1, hc2, hc3]
          ring

/-- Shifted projected step lower bound (Claim 2). -/
lemma gauss_shift_norm_sq_ge {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n)
    (A : Finset (Fin n)) (B : Finset ι) (γ : ℝ) (a : Vec n) :
    (∫ g : Vec n, ‖a + γ • walkProj v A B g‖ ^ 2 ∂(stdGaussian (Vec n))) ≥
      ‖a‖ ^ 2 + γ ^ 2 * ((n : ℝ) - (A.card : ℝ) - (B.card : ℝ)) := by
  rw [gauss_shift_norm_sq_eq v A B γ a]
  have hmul : γ ^ 2 * ((n : ℝ) - (A.card : ℝ) - (B.card : ℝ)) ≤
      γ ^ 2 * (∫ g : Vec n, ‖walkProj v A B g‖ ^ 2 ∂(stdGaussian (Vec n))) := by
    exact mul_le_mul_of_nonneg_left (gauss_proj_ge v A B) (sq_nonneg γ)
  linarith




/-! ### Part II: growth and integrability of the walk -/

/-- ‖γ • Proj‖ ≤ |γ|·‖oracle‖ pointwise (projection contracts). -/
lemma norm_proj_oracle_le {n : ℕ} {ι : Type*} [Fintype ι] (T t : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (ω : Omega n T) :
    ‖γ • Proj n T δ γ x0 v c ω t‖ ≤ |γ| * ‖oracle n T ω t‖ := by
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left
    (proj_norm_le v (frozenVars δ (Xn n T δ γ x0 v c ω t))
      (frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t)) (oracle n T ω t)) (abs_nonneg γ)

/-- Growth of the walk: ‖X_t − x0‖ ≤ |γ| Σ_{s<t} ‖g_s‖. -/
lemma norm_Xn_sub_le {n : ℕ} {ι : Type*} [Fintype ι] (T t : ℕ) (ht : t ≤ T) (δ γ : ℝ)
    (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ) (ω : Omega n T) :
    ‖Xn n T δ γ x0 v c ω t - x0‖ ≤ |γ| * ∑ s ∈ Finset.range t, ‖oracle n T ω s‖ := by
  induction t with
  | zero =>
      simp [Xn]
  | succ t ih =>
      have ht2 : t < T := Nat.lt_of_succ_le ht
      have hx : Xn n T δ γ x0 v c ω (t + 1) - x0 =
          (Xn n T δ γ x0 v c ω t - x0) + γ • Proj n T δ γ x0 v c ω t := by
        rw [Xn_succ (n := n) (T := T) δ γ x0 v c ω t ht2]
        abel
      calc
        ‖Xn n T δ γ x0 v c ω (t + 1) - x0‖
            ≤ ‖Xn n T δ γ x0 v c ω t - x0‖ + ‖γ • Proj n T δ γ x0 v c ω t‖ := by
                rw [hx]
                exact norm_add_le _ _
        _ ≤ |γ| * ∑ s ∈ Finset.range t, ‖oracle n T ω s‖ + |γ| * ‖oracle n T ω t‖ := by
                exact add_le_add (ih (Nat.le_of_lt ht2))
                  (norm_proj_oracle_le (n := n) (T := T) (t := t) δ γ x0 v c ω)
        _ = |γ| * (∑ s ∈ Finset.range t, ‖oracle n T ω s‖ + ‖oracle n T ω t‖) := by ring
        _ = |γ| * ∑ s ∈ Finset.range (t + 1), ‖oracle n T ω s‖ := by
                rw [Finset.sum_range_succ]

/-- Square growth of the walk over all T steps. -/
lemma norm_sq_Xn_sub_le {n : ℕ} {ι : Type*} [Fintype ι] (T t : ℕ) (ht : t ≤ T) (δ γ : ℝ)
    (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ) (ω : Omega n T) :
    ‖Xn n T δ γ x0 v c ω t - x0‖ ^ 2 ≤
      γ ^ 2 * (T : ℝ) * ∑ s ∈ Finset.range T, ‖oracle n T ω s‖ ^ 2 := by
  have hle := norm_Xn_sub_le (n := n) (T := T) (t := t) ht δ γ x0 v c ω
  have hsub : (∑ s ∈ Finset.range t, ‖oracle n T ω s‖) ≤
      ∑ s ∈ Finset.range T, ‖oracle n T ω s‖ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (by
      intro x hx
      exact Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Finset.mem_range.mp hx) ht))
      (fun s hs hsT => norm_nonneg _)
  have hleT : ‖Xn n T δ γ x0 v c ω t - x0‖ ≤ |γ| * (∑ s ∈ Finset.range T, ‖oracle n T ω s‖) := by
    calc
      ‖Xn n T δ γ x0 v c ω t - x0‖ ≤ |γ| * (∑ s ∈ Finset.range t, ‖oracle n T ω s‖) := hle
      _ ≤ |γ| * (∑ s ∈ Finset.range T, ‖oracle n T ω s‖) := by
          exact mul_le_mul_of_nonneg_left hsub (abs_nonneg γ)
  have hCS : ((∑ s ∈ Finset.range T, ‖oracle n T ω s‖) ^ 2) ≤
      (T : ℝ) * (∑ s ∈ Finset.range T, ‖oracle n T ω s‖ ^ 2) := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range T)
      (fun s : ℕ => (1 : ℝ)) (fun s : ℕ => ‖oracle n T ω s‖)
    simpa using hc
  calc
    ‖Xn n T δ γ x0 v c ω t - x0‖ ^ 2
        ≤ (|γ| * (∑ s ∈ Finset.range T, ‖oracle n T ω s‖)) ^ 2 := by
            exact sq_le_sq.mpr (by
              rw [abs_of_nonneg (norm_nonneg _)]
              rw [abs_of_nonneg (mul_nonneg (abs_nonneg γ)
                (Finset.sum_nonneg (fun s hs => norm_nonneg _)))]
              exact hleT)
    _ = γ ^ 2 * ((∑ s ∈ Finset.range T, ‖oracle n T ω s‖) ^ 2) := by
          have hg : (|γ| : ℝ) ^ 2 = γ ^ 2 := by simp
          rw [mul_pow, hg]
    _ ≤ γ ^ 2 * ((T : ℝ) * (∑ s ∈ Finset.range T, ‖oracle n T ω s‖ ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hCS (sq_nonneg γ)
    _ = γ ^ 2 * (T : ℝ) * (∑ s ∈ Finset.range T, ‖oracle n T ω s‖ ^ 2) := by ring

/-- ‖ω_s‖² integrable over Ω n T. -/
lemma integrable_coord_sq (n T : ℕ) (s : Fin T) :
    Integrable (fun ω : Omega n T => ‖ω s‖ ^ 2) (mu n T) := by
  have hm : MemLp id 2 (stdGaussian (Vec n)) :=
    ProbabilityTheory.IsGaussian.memLp_two_id (μ := stdGaussian (Vec n))
  have hf : Integrable (fun x : Vec n => ‖x‖ ^ 2) (stdGaussian (Vec n)) := by
    exact (memLp_two_iff_integrable_sq_norm (f := id) (μ := stdGaussian (Vec n)) hm.aestronglyMeasurable).1 hm
  simpa [Omega, mu] using
    (MeasureTheory.integrable_comp_eval (μ := fun _ : Fin T => stdGaussian (Vec n)) (i := s) hf)

/-- Sum of squared Gaussian coordinates is integrable. -/
lemma integrable_sum_oracle_sq (n T : ℕ) :
    Integrable (fun ω : Omega n T => ∑ s ∈ Finset.range T, ‖oracle n T ω s‖ ^ 2) (mu n T) := by
  refine integrable_finsetSum (Finset.range T) ?_
  intro s hs
  have hsT : s < T := Finset.mem_range.mp hs
  have hf : (fun ω : Omega n T => ‖oracle n T ω s‖ ^ 2) =
      (fun ω : Omega n T => ‖ω ⟨s, hsT⟩‖ ^ 2) := by
    funext ω
    congr 1
    rw [oracle, dif_pos hsT]
  rw [hf]
  exact integrable_coord_sq n T ⟨s, hsT⟩

/-- ‖X_t − x0‖² is integrable over Ω n T (t ≤ T). -/
lemma integrable_norm_sq_Xn {n : ℕ} {ι : Type*} [Fintype ι] (T t : ℕ) (ht : t ≤ T) (δ γ : ℝ)
    (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ) :
    Integrable (fun ω : Omega n T => ‖Xn n T δ γ x0 v c ω t - x0‖ ^ 2) (mu n T) := by
  have hsum := integrable_sum_oracle_sq n T
  have hg : Integrable (fun ω : Omega n T => (γ ^ 2 * (T : ℝ)) *
      (∑ s ∈ Finset.range T, ‖oracle n T ω s‖ ^ 2)) (mu n T) := hsum.const_mul (γ ^ 2 * (T : ℝ))
  have hX : Measurable (fun ω : Omega n T => Xn n T δ γ x0 v c ω t) :=
    measurable_Xn (n := n) (ι := ι) ht δ γ x0 v c
  have hm : Measurable (fun ω : Omega n T => ‖Xn n T δ γ x0 v c ω t - x0‖ ^ 2) := by
    exact (continuous_norm.measurable.comp (hX.sub measurable_const)).pow_const 2
  refine Integrable.mono' hg hm.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact norm_sq_Xn_sub_le (n := n) (T := T) (t := t) ht δ γ x0 v c ω



/-! ### Part III: the one-step recursion -/

/-- Position at time T of the (T+1)-walk equals the T-walk of the prefix. -/
lemma Xn_init_eq {n : ℕ} {ι : Type*} [Fintype ι] (T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (ω' : Omega n (T+1)) :
    Xn n (T+1) δ γ x0 v c ω' T = Xn n T δ γ x0 v c (Fin.init ω') T := by
  have hw : Fin.snoc (Fin.init ω') (ω' (Fin.last T)) = ω' := Fin.snoc_init_self ω'
  calc
    Xn n (T+1) δ γ x0 v c ω' T
        = Xn n (T+1) δ γ x0 v c (Fin.snoc (Fin.init ω') (ω' (Fin.last T))) T := by rw [hw]
    _ = Xn n T δ γ x0 v c (Fin.init ω') T :=
        Xn_snoc (n := n) (T := T) δ γ x0 v c (ω' (Fin.last T)) (Fin.init ω') T (le_refl T)

/-- Frozen variables grow along the (T+1)-walk from time T to time T+1. -/
lemma frozenVars_Xn_mono {n : ℕ} {ι : Type*} [Fintype ι] (T : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (ω' : Omega n (T+1)) :
    frozenVars δ (Xn n (T+1) δ γ x0 v c ω' T) ⊆
      frozenVars δ (Xn n (T+1) δ γ x0 v c ω' (T + 1)) := by
  simpa [Xn] using (frozenVars_mono δ γ x0 v c (oracle n (T+1) ω') T)

/-- Frozen rows grow along the (T+1)-walk from time T to time T+1. -/
lemma frozenRows_Xn_mono {n : ℕ} {ι : Type*} [Fintype ι] (T : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (ω' : Omega n (T+1)) :
    frozenRows δ x0 v c (Xn n (T+1) δ γ x0 v c ω' T) ⊆
      frozenRows δ x0 v c (Xn n (T+1) δ γ x0 v c ω' (T + 1)) := by
  simpa [Xn] using (frozenRows_mono δ γ x0 v c (oracle n (T+1) ω') T)

/-- Real-valued integral of a function of the prefix equals the integral on the prefix space. -/
lemma integral_init_form (n T : ℕ) (G : Omega n T → ℝ) :
    (∫ ω' : Omega n (T+1), G (Fin.init ω') ∂(mu n (T+1))) = ∫ p : Omega n T, G p ∂(mu n T) := by
  let e : Omega n (T+1) ≃ᵐ (Vec n × Omega n T) := peelEquiv n T
  have hpe : ((mu n (T+1)).map e) = ((mu n (T+1)).map (fun ω : Omega n (T+1) => (ω (Fin.last T), Fin.init ω))) := by
    congr 1
    funext ω
    simp [e, peelEquiv_apply]
  have hfun : (fun ω' : Omega n (T+1) => G (Fin.init ω')) =
      (fun y : Vec n × Omega n T => G y.2) ∘ e := by
    funext ω'
    simp [e, peelEquiv_apply]
  calc
    (∫ ω' : Omega n (T+1), G (Fin.init ω') ∂(mu n (T+1)))
        = ∫ y : Vec n × Omega n T, G y.2 ∂((mu n (T+1)).map e) := by
            rw [hfun]
            exact (integral_map_equiv e (fun y : Vec n × Omega n T => G y.2)).symm
    _ = ∫ y : Vec n × Omega n T, G y.2 ∂((stdGaussian (Vec n)).prod (mu n T)) := by
            rw [hpe, peel_measurePreserving n T]
    _ = ∫ p : Omega n T, G p ∂(mu n T) := by
            have h := integral_fun_snd (μ := stdGaussian (Vec n)) (ν := mu n T) G
            simpa using h

/-- Real-valued integral of a function of the last coordinate. -/
lemma integral_last_form (n T : ℕ) (H : Vec n → ℝ) :
    (∫ ω' : Omega n (T+1), H (ω' (Fin.last T)) ∂(mu n (T+1))) = ∫ g : Vec n, H g ∂(stdGaussian (Vec n)) := by
  let e : Omega n (T+1) ≃ᵐ (Vec n × Omega n T) := peelEquiv n T
  have hpe : ((mu n (T+1)).map e) = ((mu n (T+1)).map (fun ω : Omega n (T+1) => (ω (Fin.last T), Fin.init ω))) := by
    congr 1
    funext ω
    simp [e, peelEquiv_apply]
  have hfun : (fun ω' : Omega n (T+1) => H (ω' (Fin.last T))) =
      (fun y : Vec n × Omega n T => H y.1) ∘ e := by
    funext ω'
    simp [e, peelEquiv_apply]
  calc
    (∫ ω' : Omega n (T+1), H (ω' (Fin.last T)) ∂(mu n (T+1)))
        = ∫ y : Vec n × Omega n T, H y.1 ∂((mu n (T+1)).map e) := by
            rw [hfun]
            exact (integral_map_equiv e (fun y : Vec n × Omega n T => H y.1)).symm
    _ = ∫ y : Vec n × Omega n T, H y.1 ∂((stdGaussian (Vec n)).prod (mu n T)) := by
            rw [hpe, peel_measurePreserving n T]
    _ = ∫ g : Vec n, H g ∂(stdGaussian (Vec n)) := by
            have h := integral_fun_fst (μ := stdGaussian (Vec n)) (ν := mu n T) H
            simpa using h



/-- |frozenVars| as an integrable real function (bounded by n). -/
lemma integrable_frozenVars_card {n T t : ℕ} (ht : t ≤ T) (δ γ : ℝ) (x0 : Vec n)
    {ι : Type*} [Fintype ι] (v : ι → Vec n) (c : ι → ℝ) :
    Integrable (fun ω : Omega n T =>
        ((frozenVars δ (Xn n T δ γ x0 v c ω t)).card : ℝ)) (mu n T) := by
  have hm : Measurable (fun ω : Omega n T =>
      ((frozenVars δ (Xn n T δ γ x0 v c ω t)).card : ℝ)) :=
    measurable_frozenVars_card (n := n) (T := T) (t := t) (ht := ht) δ γ x0 v c
  refine Integrable.mono' (integrable_const (c := (n : ℝ)) (μ := mu n T)) hm.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  simpa using (Finset.card_le_univ (frozenVars δ (Xn n T δ γ x0 v c ω t)))

/-- |frozenRows| as an integrable real function (bounded by |ι|). -/
lemma integrable_frozenRows_card (n T t : ℕ) (ht : t ≤ T) (δ γ : ℝ) (x0 : Vec n)
    {ι : Type*} [Fintype ι] (v : ι → Vec n) (c : ι → ℝ) :
    Integrable (fun ω : Omega n T =>
        ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t)).card : ℝ)) (mu n T) := by
  have hm : Measurable (fun ω : Omega n T =>
      ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t)).card : ℝ)) := by
    -- analog of measurable_frozenVars_card for rows: not in LMMeas; derive from indicators
    have h : (fun ω : Omega n T =>
          ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t)).card : ℝ)) =
        fun ω => ∑ j : ι, (if j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t) then (1 : ℝ) else 0) := by
      funext ω
      rw [frozenRows_card_eq_sum' (n := n) (T := T) (t := t) (ht := ht) δ γ x0 v c ω]
    rw [h]
    exact Finset.measurable_sum Finset.univ (by
      intro j hj
      exact Measurable.ite (measurableSet_frozen_row (n := n) (ι := ι) ht δ γ x0 v c j)
        (by simp) (by simp))
  refine Integrable.mono' (integrable_const (c := (Fintype.card ι : ℝ)) (μ := mu n T))
    hm.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  simpa using (Finset.card_le_univ (frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t)))

/-- The frozen-variable cardinality integral grows with T. -/
lemma frozenVars_int_mono (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) {ι : Type*} [Fintype ι]
    (v : ι → Vec n) (c : ι → ℝ) :
    (∫ ω : Omega n T, ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T)) ≤
    (∫ ω' : Omega n (T+1), ((frozenVars δ (Xn n (T+1) δ γ x0 v c ω' (T+1))).card : ℝ)
      ∂(mu n (T+1))) := by
  have hpt (ω' : Omega n (T+1)) :
      ((frozenVars δ (Xn n (T+1) δ γ x0 v c ω' T)).card : ℝ) ≤
      ((frozenVars δ (Xn n (T+1) δ γ x0 v c ω' (T + 1))).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card (frozenVars_Xn_mono T δ γ x0 v c ω'))
  calc
    (∫ ω : Omega n T, ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T))
        = ∫ ω' : Omega n (T+1),
            ((frozenVars δ (Xn n T δ γ x0 v c (Fin.init ω') T)).card : ℝ) ∂(mu n (T+1)) := by
            rw [← integral_init_form n T (fun p : Omega n T =>
              ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ))]
    _ = ∫ ω' : Omega n (T+1),
          ((frozenVars δ (Xn n (T+1) δ γ x0 v c ω' T)).card : ℝ) ∂(mu n (T+1)) := by
          apply integral_congr_ae
          filter_upwards with ω'
          rw [Xn_init_eq (n := n) (T := T) δ γ x0 v c ω']
    _ ≤ ∫ ω' : Omega n (T+1),
          ((frozenVars δ (Xn n (T+1) δ γ x0 v c ω' (T + 1))).card : ℝ) ∂(mu n (T+1)) := by
          exact integral_mono
            (integrable_frozenVars_card (n := n) (T := T + 1) (t := T) (by omega) δ γ x0 v c)
            (integrable_frozenVars_card (n := n) (T := T + 1) (t := T + 1) (le_refl _) δ γ x0 v c)
            hpt

/-- The frozen-row cardinality integral grows with T. -/
lemma frozenRows_int_mono (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) {ι : Type*} [Fintype ι]
    (v : ι → Vec n) (c : ι → ℝ) :
    (∫ ω : Omega n T, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T)) ≤
    (∫ ω' : Omega n (T+1), ((frozenRows δ x0 v c (Xn n (T+1) δ γ x0 v c ω' (T+1))).card : ℝ)
      ∂(mu n (T+1))) := by
  have hpt (ω' : Omega n (T+1)) :
      ((frozenRows δ x0 v c (Xn n (T+1) δ γ x0 v c ω' T)).card : ℝ) ≤
      ((frozenRows δ x0 v c (Xn n (T+1) δ γ x0 v c ω' (T + 1))).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card (frozenRows_Xn_mono T δ γ x0 v c ω'))
  calc
    (∫ ω : Omega n T, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T))
        = ∫ ω' : Omega n (T+1),
            ((frozenRows δ x0 v c (Xn n T δ γ x0 v c (Fin.init ω') T)).card : ℝ) ∂(mu n (T+1)) := by
            rw [← integral_init_form n T (fun p : Omega n T =>
              ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ))]
    _ = ∫ ω' : Omega n (T+1),
          ((frozenRows δ x0 v c (Xn n (T+1) δ γ x0 v c ω' T)).card : ℝ) ∂(mu n (T+1)) := by
          apply integral_congr_ae
          filter_upwards with ω'
          rw [Xn_init_eq (n := n) (T := T) δ γ x0 v c ω']
    _ ≤ ∫ ω' : Omega n (T+1),
          ((frozenRows δ x0 v c (Xn n (T+1) δ γ x0 v c ω' (T + 1))).card : ℝ) ∂(mu n (T+1)) := by
          exact integral_mono
            (integrable_frozenRows_card (n := n) (T := T + 1) (t := T) (by omega) δ γ x0 v c)
            (integrable_frozenRows_card (n := n) (T := T + 1) (t := T + 1) (le_refl _) δ γ x0 v c)
            hpt




/-- Real (Bochner) version of the last-coordinate peel. -/
lemma integral_snoc_form (n T : ℕ) (F : Vec n → Omega n T → ℝ)
    (hint : Integrable (fun y : Vec n × Omega n T => F y.1 y.2)
      ((stdGaussian (Vec n)).prod (mu n T))) :
    (∫ ω : Omega n (T+1), F (ω (Fin.last T)) (Fin.init ω) ∂(mu n (T+1))) =
      ∫ g : Vec n, ∫ p : Omega n T, F g p ∂(mu n T) ∂(stdGaussian (Vec n)) := by
  let e : Omega n (T+1) ≃ᵐ (Vec n × Omega n T) := peelEquiv n T
  have hpe : ((mu n (T+1)).map e) = ((mu n (T+1)).map (fun ω : Omega n (T+1) => (ω (Fin.last T), Fin.init ω))) := by
    congr 1
    funext ω
    simp [e, peelEquiv_apply]
  have h1 : (∫ y : Vec n × Omega n T, F y.1 y.2 ∂((mu n (T+1)).map e)) =
      (∫ ω : Omega n (T+1), F (ω (Fin.last T)) (Fin.init ω) ∂(mu n (T+1))) := by
    rw [integral_map_equiv e (fun y : Vec n × Omega n T => F y.1 y.2)]
    congr 1
    funext ω
    simp [e, peelEquiv_apply]
  calc
    (∫ ω : Omega n (T+1), F (ω (Fin.last T)) (Fin.init ω) ∂(mu n (T+1)))
      = ∫ y : Vec n × Omega n T, F y.1 y.2 ∂((mu n (T+1)).map e) := h1.symm
    _ = ∫ y : Vec n × Omega n T, F y.1 y.2 ∂((stdGaussian (Vec n)).prod (mu n T)) := by
          rw [hpe, peel_measurePreserving n T]
    _ = ∫ g : Vec n, ∫ p : Omega n T, F g p ∂(mu n T) ∂(stdGaussian (Vec n)) := by
          exact MeasureTheory.integral_prod (fun y : Vec n × Omega n T => F y.1 y.2) hint

/-- ‖X_{T+1} − x0‖² is integrable over the peeled product. -/
lemma integrable_peel_norm_sq {n : ℕ} {ι : Type*} [Fintype ι] (T : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) :
    Integrable (fun y : Vec n × Omega n T =>
        ‖Xn n (T+1) δ γ x0 v c (Fin.snoc (α := fun _ : Fin (T+1) => Vec n) y.2 y.1) (T+1) - x0‖ ^ 2)
      ((stdGaussian (Vec n)).prod (mu n T)) := by
  let e : Omega n (T+1) ≃ᵐ (Vec n × Omega n T) := peelEquiv n T
  let H : Vec n × Omega n T → ℝ := fun y =>
    ‖Xn n (T+1) δ γ x0 v c (Fin.snoc (α := fun _ : Fin (T+1) => Vec n) y.2 y.1) (T+1) - x0‖ ^ 2
  have hpe : ((mu n (T+1)).map e) = ((mu n (T+1)).map (fun ω : Omega n (T+1) => (ω (Fin.last T), Fin.init ω))) := by
    congr 1
    funext ω
    simp [e, peelEquiv_apply]
  rw [← peel_measurePreserving n T]
  rw [← hpe]
  exact (integrable_map_equiv e H).mpr (by
    have hmain : Integrable (fun ω : Omega n (T+1) =>
        ‖Xn n (T+1) δ γ x0 v c ω (T+1) - x0‖ ^ 2) (mu n (T+1)) :=
      integrable_norm_sq_Xn (n := n) (T := T + 1) (t := T + 1) (le_refl _) δ γ x0 v c
    have hfun : (fun x : Omega n (T+1) => H (e x)) =ᵐ[mu n (T+1)]
        (fun ω : Omega n (T+1) => ‖Xn n (T+1) δ γ x0 v c ω (T+1) - x0‖ ^ 2) := by
      filter_upwards with ω
      simp only [H, e, peelEquiv_apply]
      rw [Fin.snoc_init_self]
    exact hmain.congr hfun.symm)

/-- One-step recursion: S(T+1) ≥ S(T) + γ²(n − E|A_T| − E|B_T|). -/
lemma exp_norm_sq_step {n : ℕ} {ι : Type*} [Fintype ι] (T : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) :
    (∫ ω' : Omega n (T+1), ‖Xn n (T+1) δ γ x0 v c ω' (T+1) - x0‖ ^ 2 ∂(mu n (T+1))) ≥
      (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T - x0‖ ^ 2 ∂(mu n T))
      + γ ^ 2 * ((n : ℝ)
          - (∫ ω : Omega n T, ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T))
          - (∫ ω : Omega n T, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T))) := by
  let F : Vec n → Omega n T → ℝ := fun g p =>
    ‖Xn n (T+1) δ γ x0 v c (Fin.snoc (α := fun _ : Fin (T+1) => Vec n) p g) (T+1) - x0‖ ^ 2
  have hhint : Integrable (fun y : Vec n × Omega n T => F y.1 y.2)
      ((stdGaussian (Vec n)).prod (mu n T)) := by
    simpa [F] using (integrable_peel_norm_sq (n := n) (T := T) δ γ x0 v c)
  -- peel: S(T+1) as double integral over the fresh g first
  have hpeel := integral_snoc_form n T F hhint
  have hS : (∫ ω' : Omega n (T+1), ‖Xn n (T+1) δ γ x0 v c ω' (T+1) - x0‖ ^ 2 ∂(mu n (T+1))) =
      (∫ g : Vec n, ∫ p : Omega n T, F g p ∂(mu n T) ∂(stdGaussian (Vec n))) := by
    calc
      (∫ ω' : Omega n (T+1), ‖Xn n (T+1) δ γ x0 v c ω' (T+1) - x0‖ ^ 2 ∂(mu n (T+1)))
          = (∫ ω' : Omega n (T+1), F (ω' (Fin.last T)) (Fin.init ω') ∂(mu n (T+1))) := by
              apply integral_congr_ae
              filter_upwards with ω'
              simp [F, Fin.snoc_init_self]
      _ = ∫ g : Vec n, ∫ p : Omega n T, F g p ∂(mu n T) ∂(stdGaussian (Vec n)) := hpeel
  -- swap integrals over g and p
  have hswap : (∫ g : Vec n, ∫ p : Omega n T, F g p ∂(mu n T) ∂(stdGaussian (Vec n))) =
      (∫ p : Omega n T, ∫ g : Vec n, F g p ∂(stdGaussian (Vec n)) ∂(mu n T)) := by
    exact integral_integral_swap (μ := stdGaussian (Vec n)) (ν := mu n T)
      (f := fun (g : Vec n) (p : Omega n T) => F g p) hhint
  -- pointwise bound over the fresh Gaussian
  have hpp (p : Omega n T) :
      (∫ g : Vec n, F g p ∂(stdGaussian (Vec n))) ≥
      ‖Xn n T δ γ x0 v c p T - x0‖ ^ 2
        + γ ^ 2 * ((n : ℝ)
          - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)
          - ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ)) := by
    have hpoint (g : Vec n) :
        F g p =
        ‖(Xn n T δ γ x0 v c p T - x0) + γ • walkProj v (frozenVars δ (Xn n T δ γ x0 v c p T))
            (frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)) g‖ ^ 2 := by
      have hx := last_step (T' := T) δ γ x0 v c g p
      calc
        F g p = ‖(Xn n T δ γ x0 v c p T + γ • walkProj v (frozenVars δ (Xn n T δ γ x0 v c p T))
                  (frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)) g) - x0‖ ^ 2 := by
                  simp [F, hx]
        _ = ‖(Xn n T δ γ x0 v c p T - x0) + γ • walkProj v (frozenVars δ (Xn n T δ γ x0 v c p T))
              (frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)) g‖ ^ 2 := by
              congr 1
              abel
    calc
      (∫ g : Vec n, F g p ∂(stdGaussian (Vec n)))
          = (∫ g : Vec n,
              ‖(Xn n T δ γ x0 v c p T - x0) + γ • walkProj v (frozenVars δ (Xn n T δ γ x0 v c p T))
                  (frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)) g‖ ^ 2
              ∂(stdGaussian (Vec n))) := by
              apply integral_congr_ae
              filter_upwards with g
              exact hpoint g
      _ ≥ ‖Xn n T δ γ x0 v c p T - x0‖ ^ 2
            + γ ^ 2 * ((n : ℝ)
              - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)
              - ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ)) := by
            exact gauss_shift_norm_sq_ge v (frozenVars δ (Xn n T δ γ x0 v c p T))
              (frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)) γ (Xn n T δ γ x0 v c p T - x0)
  -- integrability of the two sides of the p-integral inequality
  have hL : Integrable (fun p : Omega n T => (∫ g : Vec n, F g p ∂(stdGaussian (Vec n)))) (mu n T) := by
    have := hhint.integral_prod_right
    simpa using this
  have hR1 : Integrable (fun p : Omega n T =>
      ‖Xn n T δ γ x0 v c p T - x0‖ ^ 2) (mu n T) :=
    integrable_norm_sq_Xn (n := n) (T := T) (t := T) (le_refl _) δ γ x0 v c
  have hA := integrable_frozenVars_card (n := n) (T := T) (t := T) (le_refl _) δ γ x0 v c
  have hB := integrable_frozenRows_card (n := n) (T := T) (t := T) (le_refl _) δ γ x0 v c
  have hcst : Integrable (fun _ : Omega n T => (n : ℝ)) (mu n T) := by
    simpa using (integrable_const (c := (n : ℝ)) (μ := mu n T))
  have hR2 : Integrable (fun p : Omega n T =>
      γ ^ 2 * ((n : ℝ)
        - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)
        - ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ))) (mu n T) := by
    have h1 : Integrable (fun p : Omega n T =>
        (n : ℝ) - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)) (mu n T) := hcst.sub hA
    have h2 : Integrable (fun p : Omega n T =>
        (n : ℝ) - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)
          - ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ)) (mu n T) := h1.sub hB
    simpa [mul_comm, mul_left_comm, mul_assoc] using h2.const_mul (γ ^ 2)
  have hR : Integrable (fun p : Omega n T =>
      ‖Xn n T δ γ x0 v c p T - x0‖ ^ 2
        + γ ^ 2 * ((n : ℝ)
          - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)
          - ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ))) (mu n T) :=
    hR1.add hR2
  -- integrate the pointwise bound
  have hineq : (∫ p : Omega n T,
        (‖Xn n T δ γ x0 v c p T - x0‖ ^ 2
        + γ ^ 2 * ((n : ℝ)
          - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)
          - ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ))) ∂(mu n T)) ≤
      (∫ p : Omega n T, (∫ g : Vec n, F g p ∂(stdGaussian (Vec n))) ∂(mu n T)) := by
    exact integral_mono hR hL (fun p => hpp p)
  -- value of the right side
  have hcst : Integrable (fun _ : Omega n T => (n : ℝ)) (mu n T) := by
    simpa using (integrable_const (c := (n : ℝ)) (μ := mu n T))
  have hIntA : (∫ p : Omega n T, (n : ℝ) - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)
        ∂(mu n T)) =
      (n : ℝ) - (∫ p : Omega n T, ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T)) := by
    calc
      (∫ p : Omega n T, (n : ℝ) - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T))
          = (∫ p : Omega n T, (fun _ : Omega n T => (n : ℝ)) p
              - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T)) := rfl
      _ = (∫ p : Omega n T, (fun _ : Omega n T => (n : ℝ)) p ∂(mu n T))
            - (∫ p : Omega n T, ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T)) := by
            exact integral_sub hcst hA
      _ = (n : ℝ) - (∫ p : Omega n T, ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T)) := by
            congr 1
            rw [integral_const]
            simp
  have hInt1 : (∫ p : Omega n T,
        (n : ℝ) - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)
          - ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T)) =
      ((n : ℝ) - (∫ p : Omega n T, ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T)))
        - (∫ p : Omega n T, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T)) := by
    have hsub1 : Integrable (fun p : Omega n T =>
        (n : ℝ) - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)) (mu n T) := hcst.sub hA
    calc
      (∫ p : Omega n T,
          (n : ℝ) - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)
            - ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T))
          = (∫ p : Omega n T, (n : ℝ) - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T))
              - (∫ p : Omega n T, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T)) := by
              simpa using (integral_sub hsub1 hB)
      _ = ((n : ℝ) - (∫ p : Omega n T, ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T)))
            - (∫ p : Omega n T, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T)) := by
            rw [hIntA]
  have hInt : (∫ p : Omega n T,
      (n : ℝ) - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)
        - ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T)) =
      (n : ℝ)
      - (∫ p : Omega n T, ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T))
      - (∫ p : Omega n T, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T)) := by
    simpa using hInt1

  have hInt2 : (∫ p : Omega n T,
      γ ^ 2 * ((n : ℝ)
        - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)
        - ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ)) ∂(mu n T)) =
      γ ^ 2 * ((n : ℝ)
        - (∫ p : Omega n T, ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T))
        - (∫ p : Omega n T, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T))) := by
    calc
      (∫ p : Omega n T,
          γ ^ 2 * ((n : ℝ)
            - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)
            - ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ)) ∂(mu n T))
          = γ ^ 2 * (∫ p : Omega n T,
              (n : ℝ) - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)
                - ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T)) := by
              rw [integral_const_mul]
      _ = γ ^ 2 * ((n : ℝ)
            - (∫ p : Omega n T, ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T))
            - (∫ p : Omega n T, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ) ∂(mu n T))) := by
            rw [hInt]

  have hval : (∫ p : Omega n T,
        (‖Xn n T δ γ x0 v c p T - x0‖ ^ 2
        + γ ^ 2 * ((n : ℝ)
          - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)
          - ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ))) ∂(mu n T))
      = (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T - x0‖ ^ 2 ∂(mu n T))
        + γ ^ 2 * ((n : ℝ)
          - (∫ ω : Omega n T, ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T))
          - (∫ ω : Omega n T, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T))) := by
    calc
      (∫ p : Omega n T,
          (‖Xn n T δ γ x0 v c p T - x0‖ ^ 2
          + γ ^ 2 * ((n : ℝ)
            - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)
            - ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ))) ∂(mu n T))
          = (∫ p : Omega n T, ‖Xn n T δ γ x0 v c p T - x0‖ ^ 2 ∂(mu n T))
            + (∫ p : Omega n T,
                γ ^ 2 * ((n : ℝ)
                  - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)
                  - ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ)) ∂(mu n T)) := by
              exact integral_add hR1 hR2
      _ = (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T - x0‖ ^ 2 ∂(mu n T))
            + γ ^ 2 * ((n : ℝ)
              - (∫ ω : Omega n T, ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T))
              - (∫ ω : Omega n T, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T))) := by
              rw [hInt2]
  -- assemble
  calc
    (∫ ω' : Omega n (T+1), ‖Xn n (T+1) δ γ x0 v c ω' (T+1) - x0‖ ^ 2 ∂(mu n (T+1)))
        = (∫ p : Omega n T, (∫ g : Vec n, F g p ∂(stdGaussian (Vec n))) ∂(mu n T)) := by
            rw [hS, hswap]
    _ ≥ (∫ p : Omega n T,
          (‖Xn n T δ γ x0 v c p T - x0‖ ^ 2
          + γ ^ 2 * ((n : ℝ)
            - ((frozenVars δ (Xn n T δ γ x0 v c p T)).card : ℝ)
            - ((frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)).card : ℝ))) ∂(mu n T)) := by
            exact hineq
    _ = (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T - x0‖ ^ 2 ∂(mu n T))
          + γ ^ 2 * ((n : ℝ)
            - (∫ ω : Omega n T, ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T))
            - (∫ ω : Omega n T, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T))) := hval


/-- Moment growth: E‖X_T - x0‖² ≥ γ² T (n − E|frozenVars| − E|frozenRows|). -/
lemma exp_norm_sq_lower {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) :
    (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T - x0‖ ^ 2 ∂(mu n T)) ≥
      γ ^ 2 * (T : ℝ) *
        ((n : ℝ)
          - (∫ ω : Omega n T, ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T))
          - (∫ ω : Omega n T, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T))) := by
  induction T with
  | zero =>
      simp [Xn]
  | succ T ih =>
      -- shorthand for the cardinality integrals
      let FA : ℕ → ℝ := fun T' : ℕ =>
        (∫ ω : Omega n T', ((frozenVars δ (Xn n T' δ γ x0 v c ω T')).card : ℝ) ∂(mu n T'))
      let FB : ℕ → ℝ := fun T' : ℕ =>
        (∫ ω : Omega n T', ((frozenRows δ x0 v c (Xn n T' δ γ x0 v c ω T')).card : ℝ) ∂(mu n T'))
      change (∫ ω : Omega n (T+1), ‖Xn n (T+1) δ γ x0 v c ω (T+1) - x0‖ ^ 2 ∂(mu n (T+1))) ≥
        γ ^ 2 * ((T + 1 : ℕ) : ℝ) * ((n : ℝ) - FA (T + 1) - FB (T + 1))
      have hstep := exp_norm_sq_step (n := n) (T := T) δ γ x0 v c
      have hih : (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T - x0‖ ^ 2 ∂(mu n T)) ≥
          γ ^ 2 * (T : ℝ) * ((n : ℝ) - FA T - FB T) := by
        simpa [FA, FB] using ih
      have h1 := frozenVars_int_mono (n := n) (T := T) δ γ x0 v c
      have h2 := frozenRows_int_mono (n := n) (T := T) δ γ x0 v c
      have h1' : FA T ≤ FA (T+1) := by simpa [FA] using h1
      have h2' : FB T ≤ FB (T+1) := by simpa [FB] using h2
      have hmono : (n : ℝ) - FA (T + 1) - FB (T + 1) ≤ (n : ℝ) - FA T - FB T := by
        linarith
      have hmul : γ ^ 2 * ((T + 1 : ℕ) : ℝ) ≥ 0 := by
        positivity
      calc
        (∫ ω : Omega n (T+1), ‖Xn n (T+1) δ γ x0 v c ω (T+1) - x0‖ ^ 2 ∂(mu n (T+1)))
            ≥ (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T - x0‖ ^ 2 ∂(mu n T))
              + γ ^ 2 * ((n : ℝ) - FA T - FB T) := by
              simpa [FA, FB] using hstep
        _ ≥ γ ^ 2 * (T : ℝ) * ((n : ℝ) - FA T - FB T)
              + γ ^ 2 * ((n : ℝ) - FA T - FB T) := by
              linarith
        _ = γ ^ 2 * (((T : ℝ) + 1) * ((n : ℝ) - FA T - FB T)) := by ring
        _ = γ ^ 2 * (((T + 1 : ℕ) : ℝ) * ((n : ℝ) - FA T - FB T)) := by
              norm_num
        _ ≥ γ ^ 2 * ((T + 1 : ℕ) : ℝ) * ((n : ℝ) - FA (T + 1) - FB (T + 1)) := by
              -- γ²(T+1) ≥ 0 and monotone
              have hmono' : ((n : ℝ) - FA (T+1) - FB (T+1)) ≤ ((n : ℝ) - FA T - FB T) := hmono
              have hle0 : 0 ≤ γ ^ 2 * ((T + 1 : ℕ) : ℝ) := by positivity
              nlinarith


end Discrepancy

end Submission
