import Mathlib
import Submission.MatSpace
import Submission.GenProc
import Submission.Commons.Topology.MetricSpace.exists_finset_sphere_net
import Submission.Commons.Analysis.InnerProductSpace.quadform_le_of_sphere_net

/-!
# The maximal operator-norm bound

Combining the maximal Gaussian tail for a single linear functional (`maximal_tail_incr`) with an
`1/4`-net of the unit sphere and the elementary fact that a quadratic form is bounded by twice
its values on such a net gives

`P(∃ k ≤ K, λ_max(A_k - a₀·Id) ≥ 2r) ≤ |net| · 8 exp(-r²/(2Kε²))`.

With `|net| ≤ C^d` and `r = C₀ √(Kε² d)` this is `≤ e^{-d}` for a large constant `C₀`, so
`λ_max(A_k) = a₀ + O(√(T d)) = 1 + o(1)` uniformly over all `k ≤ K`.
-/

namespace Submission.OpNorm

open Matrix MeasureTheory ProbabilityTheory
open Submission.MatSpace
open Submission.GenProc

noncomputable section

variable {d : ℕ} (pl : MatV d → MatV d →L[ℝ] MatV d) (a₀ ε : ℝ) (K : ℕ)

lemma inner_tensorV (x y : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (tensorV x) (tensorV y) = (inner ℝ x y) ^ 2 := by
  have hx : inner ℝ x y = ∑ i, x i * y i := by
    rw [PiLp.inner_apply]; simp [RCLike.inner_apply, mul_comm]
  have hxy : inner ℝ (tensorV x) (tensorV y)
      = ∑ p : Fin d × Fin d, (x p.1 * x p.2) * (y p.1 * y p.2) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [RCLike.inner_apply, conj_trivial, tensorV]
    ring
  rw [hxy, hx, sq, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma norm_tensorV (x : EuclideanSpace ℝ (Fin d)) : ‖tensorV x‖ = ‖x‖ ^ 2 := by
  have h : ‖tensorV x‖ ^ 2 = (‖x‖ ^ 2) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_tensorV, real_inner_self_eq_norm_sq]
  have h1 : 0 ≤ ‖tensorV x‖ := norm_nonneg _
  have h2 : 0 ≤ ‖x‖ ^ 2 := by positivity
  nlinarith [sq_nonneg (‖tensorV x‖ - ‖x‖ ^ 2)]

/-- The quadratic form is the inner product with the rank-one tensor. -/
lemma quadFormV_eq_inner (M : MatV d) (x : EuclideanSpace ℝ (Fin d)) :
    quadFormV M x = inner ℝ M (tensorV x) :=
  quadLin_eq_inner x M

/-- **The state as a sum of increments**, in quadratic-form form. -/
lemma quadFormV_state_sub {k : ℕ} (hk : k ≤ K) (ω : Fin K → MatV d × MatV d)
    (y : EuclideanSpace ℝ (Fin d)) :
    quadFormV (proc pl a₀ ε K ω k - a₀ • oneV d) y
      = ∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
          ε * inner ℝ (incrAt pl a₀ ε K ω j) (tensorV y) := by
  rw [quadFormV_eq_inner]
  have hmk : proc pl a₀ ε K ω k - a₀ • oneV d
      = ∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
          ε • incrAt pl a₀ ε K ω j := by
    rw [proc_eq_sum (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hk ω]; abel
  rw [hmk, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left]

/-- The quadratic form of the state is symmetric. -/
lemma symm_state_sub (hG : ∀ A : MatV d, Good (pl A)) (k : ℕ)
    (ω : Fin K → MatV d × MatV d) :
    (matOf d (proc pl a₀ ε K ω k - a₀ • oneV d)).IsSymm := by
  rw [← mem_symV]
  exact (symV d).sub_mem (proc_mem_symV (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hG k ω)
    ((symV d).smul_mem a₀ (oneV_mem_symV d))

/-- **Maximal operator-norm bound.**  For a `1/4`-net `S` of the unit sphere,
`P(∃k ≤ K, ∃‖x‖ = 1, |⟪A_k - a₀·Id, x ⊗ x⟫| ≥ 2r) ≤ |S| · 8 exp(-r²/(2Kε²))`. -/
theorem maximal_tail_quadform (hpl : Measurable pl) (hG : ∀ A : MatV d, Good (pl A))
    {ε : ℝ} (hε : 0 ≤ ε) {r : ℝ} (hr : 0 ≤ r)
    (S : Finset (EuclideanSpace ℝ (Fin d))) (hSun : ∀ x ∈ S, ‖x‖ = 1)
    (hcover : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ 1 / 4) :
    (sampleLaw d K).real {ω | ∃ k ≤ K, ∃ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 ∧
        2 * r < |quadFormV (proc pl a₀ ε K ω k - a₀ • oneV d) x|}
      ≤ (S.card : ℝ) * (8 * Real.exp (-r ^ 2 / (2 * (K : ℝ) * ε ^ 2))) := by
  classical
  set E : EuclideanSpace ℝ (Fin d) → Set (Fin K → MatV d × MatV d) := fun x =>
    {ω | ∃ k ≤ K, r < |∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
        ε * inner ℝ (incrAt pl a₀ ε K ω j) (tensorV x)|} with hE
  have heach : ∀ x ∈ S, (sampleLaw d K).real (E x)
      ≤ 8 * Real.exp (-r ^ 2 / (2 * (K : ℝ) * ε ^ 2)) := by
    intro x hx
    have hW : ‖tensorV x‖ ≤ 1 := by rw [norm_tensorV, hSun x hx]; norm_num
    have hmain := maximal_tail_incr (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl hG
      (tensorV x) hW hε hr
    refine le_trans (MeasureTheory.measureReal_mono ?_ (MeasureTheory.measure_ne_top _ _)) hmain
    intro ω hω
    obtain ⟨k, hk, hlt⟩ := hω
    exact ⟨k, hk, le_of_lt hlt⟩
  have hsub : {ω | ∃ k ≤ K, ∃ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 ∧
        2 * r < |quadFormV (proc pl a₀ ε K ω k - a₀ • oneV d) x|}
      ⊆ ⋃ x ∈ S, E x := by
    rintro ω ⟨k, hk, x, hx1, hlt⟩
    by_contra hcon
    have hnet : ∀ y ∈ S, |quadFormV (proc pl a₀ ε K ω k - a₀ • oneV d) y| ≤ r := by
      intro y hy
      have h3 : ¬ ∃ k' ≤ K, r < |∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k'),
          ε * inner ℝ (incrAt pl a₀ ε K ω j) (tensorV y)| := fun hmem =>
        hcon (Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, hmem⟩⟩)
      have h4 : ¬ (r < |∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
          ε * inner ℝ (incrAt pl a₀ ε K ω j) (tensorV y)|) := fun hlt' => h3 ⟨k, hk, hlt'⟩
      rw [not_lt] at h4
      rwa [quadFormV_state_sub (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hk ω y]
    have hnet' : ∀ y ∈ S, |∑ i, ∑ j, (matOf d (proc pl a₀ ε K ω k - a₀ • oneV d)) i j
        * y i * y j| ≤ r := by
      intro y hy
      have := hnet y hy
      simpa [quadFormV] using this
    have hall := Commons.Analysis.InnerProductSpace.quadform_le_of_sphere_net
      (matOf d (proc pl a₀ ε K ω k - a₀ • oneV d))
      (symm_state_sub (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hG k ω)
      hr S hSun hcover hnet' x
    simp only [hx1, one_pow, mul_one] at hall
    have hqx : quadFormV (proc pl a₀ ε K ω k - a₀ • oneV d) x
        = ∑ i, ∑ j, (matOf d (proc pl a₀ ε K ω k - a₀ • oneV d)) i j * x i * x j := rfl
    rw [hqx] at hlt
    linarith
  calc (sampleLaw d K).real _
      ≤ (sampleLaw d K).real (⋃ x ∈ S, E x) :=
        MeasureTheory.measureReal_mono hsub (MeasureTheory.measure_ne_top _ _)
    _ ≤ ∑ x ∈ S, (sampleLaw d K).real (E x) :=
        MeasureTheory.measureReal_biUnion_finset_le S E
    _ ≤ ∑ x ∈ S, 8 * Real.exp (-r ^ 2 / (2 * (K : ℝ) * ε ^ 2)) :=
        Finset.sum_le_sum heach
    _ = (S.card : ℝ) * (8 * Real.exp (-r ^ 2 / (2 * (K : ℝ) * ε ^ 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul]

section Corollaries

variable {ε : ℝ}

lemma quadFormV_add (A B : MatV d) (x : EuclideanSpace ℝ (Fin d)) :
    quadFormV (A + B) x = quadFormV A x + quadFormV B x := by
  rw [show quadFormV (A + B) x
      = ∑ i, ∑ j, (A + B) (i, j) * x i * x j from rfl,
    show quadFormV A x = ∑ i, ∑ j, A (i, j) * x i * x j from rfl,
    show quadFormV B x = ∑ i, ∑ j, B (i, j) * x i * x j from rfl]
  rw [show (∑ i, ∑ j, (A + B) (i, j) * x i * x j)
      = ∑ i, ((∑ j, A (i, j) * x i * x j) + (∑ j, B (i, j) * x i * x j)) from by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [PiLp.add_apply]; ring]
  rw [Finset.sum_add_distrib]

lemma quadFormV_smul (c : ℝ) (A : MatV d) (x : EuclideanSpace ℝ (Fin d)) :
    quadFormV (c • A) x = c * quadFormV A x := by
  rw [show quadFormV (c • A) x = ∑ i, ∑ j, (c • A) (i, j) * x i * x j from rfl,
    show quadFormV A x = ∑ i, ∑ j, A (i, j) * x i * x j from rfl]
  rw [show (∑ i, ∑ j, (c • A) (i, j) * x i * x j)
      = ∑ i, c * (∑ j, A (i, j) * x i * x j) from by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [PiLp.smul_apply]; ring]
  rw [Finset.mul_sum]

/-- `x ⬝ᵥ x = ‖x‖²` for vectors of a Euclidean space. -/
lemma dotProduct_self (x : EuclideanSpace ℝ (Fin d)) : x ⬝ᵥ x = ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rfl

lemma quadFormV_oneV (c : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    quadFormV (c • oneV d) x = c * ‖x‖ ^ 2 := by
  rw [quadFormV_smul]
  congr 1
  rw [quadFormV_eq_dotProduct]
  rw [matOf_oneV, Matrix.one_mulVec, dotProduct_self]

/-- **Net version with the cardinality bound built in.** -/
theorem maximal_tail_quadform_exists (hpl : Measurable pl) (hG : ∀ A : MatV d, Good (pl A))
    {ε : ℝ} (hε : 0 ≤ ε) {r : ℝ} (hr : 0 ≤ r) :
    ∃ C : ℝ, 1 ≤ C ∧
      (sampleLaw d K).real {ω | ∃ k ≤ K, ∃ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 ∧
          2 * r < |quadFormV (proc pl a₀ ε K ω k - a₀ • oneV d) x|}
        ≤ (4 * C) ^ d * (8 * Real.exp (-r ^ 2 / (2 * (K : ℝ) * ε ^ 2))) := by
  obtain ⟨S, hSun, hcover, C, hC1, hcard⟩ :=
    Commons.Topology.MetricSpace.exists_finset_sphere_net d
      (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 : ℝ) / 4 ≤ 1)
  refine ⟨C, hC1, le_trans
    (maximal_tail_quadform (pl := pl) (a₀ := a₀) (K := K) hpl hG hε hr S hSun hcover) ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [show C / (1 / 4) = 4 * C from by ring] at hcard
  exact hcard

/-- Homogeneity of the quadratic form in the vector variable. -/
lemma quadFormV_smul_right (M : MatV d) (c : ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    quadFormV M (c • y) = c ^ 2 * quadFormV M y := by
  rw [show quadFormV M (c • y) = ∑ i, ∑ j, M (i, j) * (c • y) i * (c • y) j from rfl,
    show quadFormV M y = ∑ i, ∑ j, M (i, j) * y i * y j from rfl]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PiLp.smul_apply, PiLp.smul_apply]
  ring

end Corollaries

end

end Submission.OpNorm
