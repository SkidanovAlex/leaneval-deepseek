import Mathlib
import Submission.Commons.Analysis.Fourier.bourgain_entropy_integral_l2_fixed
import Submission.Commons.Analysis.Fourier.lintegral_translate_sub_sq_le_of_fourier_support

set_option maxHeartbeats 8000000

open _root_.MeasureTheory Finset
open scoped BigOperators _root_.ENNReal FourierTransform

set_option maxHeartbeats 800000

namespace Commons.Analysis.Fourier

noncomputable section

/-- The `k`-th band symbol `1_{[λ-h,λ+h]}·φ((·-λ)/h)` as a complex-valued function. -/
def bandSym (φ : ℝ → ℝ) (lamk h : ℝ) : ℝ → ℂ :=
  (Set.Icc (lamk - h) (lamk + h)).indicator fun θ => (φ ((θ - lamk) / h) : ℂ)

lemma bandSym_apply (φ : ℝ → ℝ) (lamk h θ : ℝ) :
    bandSym φ lamk h θ =
      if θ ∈ Set.Icc (lamk - h) (lamk + h) then (φ ((θ - lamk) / h) : ℂ) else 0 :=
  Set.indicator_apply _ _ _

lemma bandSym_measurable {φ : ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ) (lamk h : ℝ) :
    Measurable (bandSym φ lamk h) := by
  refine Measurable.indicator ?_ measurableSet_Icc
  exact Complex.measurable_ofReal.comp ((hφ 1).continuous.measurable.comp (by fun_prop))

lemma bandSym_bound {φ : ℝ → ℝ} (hbd : ∀ x : ℝ, |φ x| ≤ 2) (lamk h θ : ℝ) :
    ‖bandSym φ lamk h θ‖ ≤ 2 := by
  rw [bandSym_apply]
  split
  · rw [Complex.norm_real, Real.norm_eq_abs]; exact hbd _
  · simp

/-- The total band symbol `∑_k bandSym φ (λ_k) h`. -/
def bandSumSym {K : ℕ} (φ : ℝ → ℝ) (lam : Fin K → ℝ) (h : ℝ) : ℝ → ℂ :=
  fun θ => ∑ k : Fin K, bandSym φ (lam k) h θ

lemma bandSumSym_measurable {K : ℕ} {φ : ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ)
    (lam : Fin K → ℝ) (h : ℝ) : Measurable (bandSumSym φ lam h) :=
  Finset.measurable_sum _ (fun k _ => bandSym_measurable hφ _ _)

lemma bandSumSym_bound {K : ℕ} {φ : ℝ → ℝ} (hbd : ∀ x : ℝ, |φ x| ≤ 2)
    (lam : Fin K → ℝ) (h θ : ℝ) : ‖bandSumSym φ lam h θ‖ ≤ 2 * K := by
  calc ‖bandSumSym φ lam h θ‖ ≤ ∑ k : Fin K, ‖bandSym φ (lam k) h θ‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin K, (2:ℝ) := Finset.sum_le_sum (fun k _ => bandSym_bound hbd _ _ _)
    _ = 2 * K := by simp [mul_comm]

/-- A nonnegative bound for the `λ_k`. -/
lemma exists_abs_bound {K : ℕ} (lam : Fin K → ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ k : Fin K, |lam k| ≤ M := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    exact ⟨0, le_refl 0, fun k => absurd k.isLt (Nat.not_lt_zero k.val)⟩
  · haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
    obtain ⟨k0, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin K))
      (fun k => |lam k|) Finset.univ_nonempty
    exact ⟨|lam k0|, abs_nonneg _, fun k => hmax k (Finset.mem_univ k)⟩

lemma bandSumSym_support_measure_ne_top {K : ℕ} {φ : ℝ → ℝ} (lam : Fin K → ℝ) (h : ℝ) :
    (volume : Measure ℝ) (Function.support (bandSumSym φ lam h)) ≠ ∞ := by
  obtain ⟨M, hMnn, hM⟩ := exists_abs_bound lam
  have hsub : Function.support (bandSumSym φ lam h) ⊆ Set.Icc (-(M + |h|)) (M + |h|) := by
    intro θ hθ
    by_contra hcon
    apply hθ
    rw [bandSumSym]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [bandSym_apply, if_neg]
    intro hmem
    simp only [Set.mem_Icc, not_and_or, not_le] at hcon hmem
    have hkle := abs_le.mp (hM k)
    rcases hcon with hc | hc
    · have h3 : lam k < -M := by linarith [hmem.1, hc, le_abs_self h]
      have : M < |lam k| := by
        rw [abs_of_neg (by linarith)]
        linarith
      linarith [hkle.2]
    · have h3 : M < lam k := by linarith [hmem.2, hc, le_abs_self h]
      have : M < |lam k| := by
        rw [abs_of_pos (by linarith)]
        linarith
      linarith [hkle.1]
  refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

lemma bandSumSym_memLp_one {K : ℕ} {φ : ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ)
    (hbd : ∀ x : ℝ, |φ x| ≤ 2) (lam : Fin K → ℝ) (h : ℝ) :
    MemLp (bandSumSym φ lam h) 1 (volume : Measure ℝ) :=
  (memLp_top_of_bound (bandSumSym_measurable hφ lam h).aestronglyMeasurable _
      (Filter.Eventually.of_forall (fun θ => bandSumSym_bound hbd lam h θ))
    ).mono_exponent_of_measure_support_ne_top
      (s := Function.support (bandSumSym φ lam h)) (fun _ hx => Function.notMem_support.mp hx)
      (bandSumSym_support_measure_ne_top lam h) le_top

lemma bandSumSym_memLp_two {K : ℕ} {φ : ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ)
    (hbd : ∀ x : ℝ, |φ x| ≤ 2) (lam : Fin K → ℝ) (h : ℝ) :
    MemLp (bandSumSym φ lam h) 2 (volume : Measure ℝ) :=
  (memLp_top_of_bound (bandSumSym_measurable hφ lam h).aestronglyMeasurable _
      (Filter.Eventually.of_forall (fun θ => bandSumSym_bound hbd lam h θ))
    ).mono_exponent_of_measure_support_ne_top
      (s := Function.support (bandSumSym φ lam h)) (fun _ hx => Function.notMem_support.mp hx)
      (bandSumSym_support_measure_ne_top lam h) le_top

lemma bandSumSym_memLp_top {K : ℕ} {φ : ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ)
    (hbd : ∀ x : ℝ, |φ x| ≤ 2) (lam : Fin K → ℝ) (h : ℝ) :
    MemLp (bandSumSym φ lam h) ⊤ (volume : Measure ℝ) :=
  memLp_top_of_bound (bandSumSym_measurable hφ lam h).aestronglyMeasurable _
    (Filter.Eventually.of_forall (fun θ => bandSumSym_bound hbd lam h θ))

end

end Commons.Analysis.Fourier


/-!
# The `ℓ²`-vector form of Bourgain's entropy integral (Lemma 3.33)

The published `Commons.Analysis.Fourier.bourgain_entropy_integral_l2_fixed` measures the metric
entropy of the windowed curve `t ↦ ((f k * Ψ_t)(x))_k` in the **supremum** norm on `Fin K → ℂ`.
The chain estimate `Commons.Analysis.Fourier.chain_exp_sum_le_entropy` however controls nets with
**`ℓ²`** radii, and the `ℓ²`-covering number is larger than the sup one.  This file proves the
`ℓ²` form: the curve is regarded as a map into `EuclideanSpace ℂ (Fin K)` and the entropy integral
is controlled by `‖Ψ‖_∞` and `log²(K+2)`, with the vector-valued variation bound obtained from the
scalar variation bound by Minkowski's inequality.
-/

namespace Commons.Analysis.Fourier

open _root_.MeasureTheory _root_.Metric
open scoped _root_.ENNReal _root_.Topology BigOperators

noncomputable section

variable {K : ℕ}

/-- The windowed dilation curve, as a map into the Euclidean space `EuclideanSpace ℂ (Fin K)`. -/
noncomputable def winCurveL2 (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) :
    {t : ℝ // 0 < t} → EuclideanSpace ℂ (Fin K) :=
  fun t => WithLp.toLp 2 (fun k : Fin K =>
    ∫ y : ℝ, f k y * ((t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / (t : ℝ))))

@[simp] lemma winCurveL2_apply (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ)
    (t : {t : ℝ // 0 < t}) (k : Fin K) :
    winCurveL2 Ψ f x t k = ∫ y : ℝ, f k y * ((t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / (t : ℝ))) :=
  rfl

/-- The logarithmic reparametrisation of `winCurveL2`. -/
noncomputable def winCurveRL2 (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) :
    ℝ → EuclideanSpace ℂ (Fin K) :=
  fun u => winCurveL2 Ψ f x ⟨Real.exp u, Real.exp_pos u⟩

/-- The `ℓ²`-valued `s`-variation of the curve `winCurveL2` over the scales `t > 0`. -/
noncomputable def winVarVecL2 (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) (s : ℝ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (u : Fin (J + 1) → {t : ℝ // 0 < t}),
    ⨆ (_ : StrictMono (fun j => (u j : ℝ))),
      ENNReal.ofReal ((∑ j : Fin J,
        ‖winCurveL2 Ψ f x (u (Fin.castSucc j)) - winCurveL2 Ψ f x (u (Fin.succ j))‖ ^ s)
          ^ ((1:ℝ)/s))

/-- The entropy-number integrand of the `ℓ²`-valued curve. -/
noncomputable def winML2 (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) (l : ℝ) : ENNReal :=
  (((Metric.coveringNumber l.toNNReal (Set.range (winCurveL2 Ψ f x)) : ℕ∞) : ENNReal) - 1)

/-- The `ℝ≥0∞`-valued supremum of the `ℓ²`-valued curve. -/
noncomputable def winFL2 (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) : ENNReal :=
  ⨆ (t : {t : ℝ // 0 < t}), ‖winCurveL2 Ψ f x t‖ₑ

/-- The range of the logarithmically reparametrised curve is the range of the curve. -/
lemma range_winCurveRL2 (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) :
    Set.range (winCurveRL2 Ψ f x) = Set.range (winCurveL2 Ψ f x) := by
  have h1 : Set.range (winCurveRL2 Ψ f x)
      = Set.range (winCurveL2 Ψ f x ∘ fun u : ℝ =>
          (⟨Real.exp u, Real.exp_pos u⟩ : {t : ℝ // 0 < t})) := rfl
  have h2 : Set.range (fun u : ℝ => (⟨Real.exp u, Real.exp_pos u⟩ : {t : ℝ // 0 < t}))
      = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro t
    exact ⟨Real.log t.1, Subtype.ext (Real.exp_log t.2)⟩
  rw [h1, Set.range_comp, h2, Set.image_univ]

/-- The tuple sums of the logarithmically reparametrised curve are bounded by `winVarVecL2`. -/
lemma winVarVecL2_tuple_bound (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) {s : ℝ}
    (J : ℕ) (u : Fin (J + 1) → ℝ) (hu : StrictMono u) :
    ENNReal.ofReal ((∑ j : Fin J, dist (winCurveRL2 Ψ f x (u (Fin.castSucc j)))
        (winCurveRL2 Ψ f x (u (Fin.succ j))) ^ s) ^ ((1:ℝ)/s)) ≤ winVarVecL2 Ψ f x s := by
  simp only [winCurveRL2, winVarVecL2, dist_eq_norm]
  refine le_iSup_of_le J (le_iSup_of_le (fun j => (⟨Real.exp (u j), Real.exp_pos _⟩ :
    {t : ℝ // 0 < t})) ?_)
  refine le_iSup_of_le ?_ le_rfl
  intro i j hij
  show (Real.exp (u i) : ℝ) < Real.exp (u j)
  exact Real.exp_lt_exp.mpr (hu hij)

/-- In the Euclidean space the `enorm` of a vector is the `ℓ²` combination of the coordinates. -/
lemma enorm_eq_sqrt_sum_L2 (v : EuclideanSpace ℂ (Fin K)) :
    ‖v‖ₑ = (∑ k : Fin K, ‖v k‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
  have h1 : (∑ k : Fin K, ‖v k‖ₑ ^ (2:ℝ))
      = ENNReal.ofReal (∑ k : Fin K, ‖v k‖ ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [enorm_eq_ofReal_norm',
      show ENNReal.ofReal ‖v k‖ ^ (2:ℝ) = ENNReal.ofReal (‖v k‖ ^ 2) by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
          ENNReal.ofReal_pow (norm_nonneg _)]]
  rw [h1, enorm_eq_ofReal_norm', EuclideanSpace.norm_eq, Real.sqrt_eq_rpow,
    ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)
      (by norm_num : (0:ℝ) ≤ 1/2)]

end

namespace MinkowskiInterlude

/-! ### Minkowski's inequality for finite sums -/

/-- **Minkowski's inequality for finite sums.**  For `2 < s` and nonnegative `b`, the `ℓ^s(ℓ²)`
norm is bounded by the `ℓ²(ℓ^s)` norm:
`(∑_j (∑_k b j k²)^{s/2})^{1/s} ≤ (∑_k (∑_j b j k^s)^{2/s})^{1/2}`. -/
theorem minkowski_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → κ → ℝ)
    (hb : ∀ j k, 0 ≤ b j k) {s : ℝ} (hs : 2 < s) :
    (∑ j, (∑ k, b j k ^ (2:ℝ)) ^ (s / 2)) ^ (1 / s)
      ≤ (∑ k, (∑ j, b j k ^ s) ^ (2 / s)) ^ ((1:ℝ) / 2) := by
  have hs0 : 0 < s := by linarith
  set A : ι → ℝ := fun j => (∑ k, b j k ^ (2:ℝ)) ^ ((1:ℝ)/2) with hA
  have hsum : ∀ j, 0 ≤ ∑ k, b j k ^ (2:ℝ) := fun j =>
    Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (hb j k) 2)
  have hAnn : ∀ j, 0 ≤ A j := fun j => by
    rw [hA]; beta_reduce
    exact Real.rpow_nonneg (hsum j) ((1:ℝ)/2)
  have hAsq : ∀ j, (A j) ^ (2:ℝ) = ∑ k, b j k ^ (2:ℝ) := fun j => by
    rw [hA]; beta_reduce
    rw [← Real.rpow_mul (hsum j), show ((1:ℝ)/2) * 2 = 1 by norm_num, Real.rpow_one]
  have hAs : ∀ j, (A j) ^ s = (∑ k, b j k ^ (2:ℝ)) ^ (s / 2) := fun j => by
    rw [hA]; beta_reduce
    rw [← Real.rpow_mul (hsum j)]
    congr 1
    ring
  have hAsplit : ∀ j, (A j) ^ s = (A j) ^ (s - 2) * (A j) ^ (2:ℝ) := fun j => by
    rw [← Real.rpow_add' (hAnn j) (by linarith : (s - 2) + 2 ≠ 0)]
    congr 1
    ring
  -- Hölder step
  have hpq : Real.HolderConjugate (s / (s - 2)) (s / 2) :=
    ⟨by field_simp; ring, by positivity, by positivity⟩
  have hholder : ∀ k, ∑ j, (A j) ^ (s - 2) * (b j k) ^ (2:ℝ)
      ≤ (∑ j, (A j) ^ s) ^ ((s-2)/s) * (∑ j, (b j k) ^ s) ^ (2/s) := by
    intro k
    have h := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hpq
      (f := fun j => (A j) ^ (s - 2)) (g := fun j => (b j k) ^ (2:ℝ))
      (fun j _ => Real.rpow_nonneg (hAnn j) _) (fun j _ => Real.rpow_nonneg (hb j k) 2)
    have h1 : ∀ j, ((A j) ^ (s - 2)) ^ (s / (s - 2)) = (A j) ^ s := by
      intro j
      rw [← Real.rpow_mul (hAnn j)]
      congr 1
      have hne : s - 2 ≠ 0 := by linarith
      field_simp
    have h2 : ∀ j, ((b j k) ^ (2:ℝ)) ^ (s / 2) = (b j k) ^ s := by
      intro j
      rw [← Real.rpow_mul (hb j k)]
      ring_nf
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_congr rfl (fun j _ => h2 j)] at h
    have e1 : (1 / (s / (s - 2))) = (s - 2) / s := by
      field_simp
    have e2 : (1 / (s / 2)) = 2 / s := by
      field_simp
    rw [e1, e2] at h
    exact h
  have hB : ∑ j, (A j) ^ s
      ≤ (∑ j, (A j) ^ s) ^ ((s-2)/s) * ∑ k, (∑ j, (b j k) ^ s) ^ (2/s) := by
    calc ∑ j, (A j) ^ s = ∑ j, (A j) ^ (s - 2) * (A j) ^ (2:ℝ) :=
          Finset.sum_congr rfl fun j _ => hAsplit j
      _ = ∑ j, (A j) ^ (s - 2) * ∑ k, (b j k) ^ (2:ℝ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hAsq j]
      _ = ∑ j, ∑ k, (A j) ^ (s - 2) * (b j k) ^ (2:ℝ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ k, ∑ j, (A j) ^ (s - 2) * (b j k) ^ (2:ℝ) := Finset.sum_comm
      _ ≤ ∑ k, (∑ j, (A j) ^ s) ^ ((s-2)/s) * (∑ j, (b j k) ^ s) ^ (2/s) :=
          Finset.sum_le_sum fun k _ => hholder k
      _ = (∑ j, (A j) ^ s) ^ ((s-2)/s) * ∑ k, (∑ j, (b j k) ^ s) ^ (2/s) := by
          rw [Finset.mul_sum]
  set B : ℝ := ∑ j, (A j) ^ s with hBdef
  set C : ℝ := ∑ k, (∑ j, (b j k) ^ s) ^ (2/s) with hCdef
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hAnn j) _
  have hCnn : 0 ≤ C := Finset.sum_nonneg fun k _ =>
    Real.rpow_nonneg (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hb j k) s) _
  have hBC : B ≤ B ^ ((s-2)/s) * C := hB
  have hLHS : (∑ j, (∑ k, b j k ^ (2:ℝ)) ^ (s / 2)) = B := by
    rw [hBdef]
    exact Finset.sum_congr rfl fun j _ => (hAs j).symm
  rw [hLHS]
  rcases eq_or_lt_of_le hBnn with hB0 | hBpos
  · rw [← hB0, Real.zero_rpow (by positivity : (1/s : ℝ) ≠ 0)]
    exact Real.rpow_nonneg hCnn _
  · have hexp : 2/s + (s-2)/s = (1:ℝ) := by
      have hsne : s ≠ 0 := hs0.ne'
      field_simp
      ring
    have hBeq : B = B ^ (2/s) * B ^ ((s-2)/s) := by
      have h1 : B ^ (2/s) * B ^ ((s-2)/s) = B ^ (2/s + (s-2)/s) :=
        (Real.rpow_add' hBpos.le (by rw [hexp]; norm_num)).symm
      rw [h1, hexp, Real.rpow_one]
    have hdiv : B ^ (2/s) ≤ C := by
      have hpos : 0 < B ^ ((s-2)/s) := Real.rpow_pos_of_pos hBpos _
      have h2 : B ^ (2/s) * B ^ ((s-2)/s) ≤ C * B ^ ((s-2)/s) := by
        rw [← hBeq]
        exact hBC.trans (le_of_eq (mul_comm _ _))
      exact le_of_mul_le_mul_right h2 hpos
    calc B ^ (1 / s) = (B ^ (2 / s)) ^ ((1:ℝ) / 2) := by
          rw [← Real.rpow_mul hBnn]
          congr 1
          field_simp
      _ ≤ C ^ ((1:ℝ) / 2) := Real.rpow_le_rpow (Real.rpow_nonneg hBnn _) hdiv (by norm_num)

end MinkowskiInterlude

open MinkowskiInterlude

variable {K : ℕ}

/-- Squares of `ofReal`s. -/
lemma ofReal_rpow_two_eq {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal (x ^ (2:ℝ)) = ENNReal.ofReal x ^ (2:ℝ) :=
  (ENNReal.ofReal_rpow_of_nonneg hx (by norm_num : (0:ℝ) ≤ 2)).symm

/-! ### The pointwise entropy-versus-variation bound in the `ℓ²` metric -/

end Commons.Analysis.Fourier


/-!
# The band-operator framework for the smooth-window maximal estimate

Definitions and elementary estimates for the fixed-window maximal estimate of Bourgain's
Lemma 4.13: the dyadic band operator `bandOpD`, its energy `bandSq`, its maximal function
`bandMax`, and the translation operators.
-/

namespace Commons.Analysis.Fourier

open _root_.MeasureTheory Finset Function Filter
open scoped _root_.ENNReal _root_.Topology BigOperators FourierTransform

noncomputable section

variable {K : ℕ}

/-! ### Dilated Schwartz windows -/

/-- The affine map `u ↦ (x - u)/t`. -/
noncomputable def dilFun (x t : ℝ) : ℝ → ℝ := fun u => (x - u)/t

lemma dilFun_temp (x t : ℝ) : (dilFun x t).HasTemperateGrowth := by
  unfold dilFun
  exact ((HasTemperateGrowth.const x).sub HasTemperateGrowth.id').mul
    (HasTemperateGrowth.const _)

lemma dilFun_anti (x t : ℝ) (ht : t ≠ 0) :
    AntilipschitzWith (Real.toNNReal |t|) (dilFun x t) := by
  refine AntilipschitzWith.of_le_mul_dist fun u v => ?_
  have htv : (↑(Real.toNNReal |t|) : ℝ) = |t| := Real.coe_toNNReal _ (abs_nonneg t)
  have hd : dilFun x t u - dilFun x t v = -((u - v)/t) := by unfold dilFun; ring
  have hmain : |t| * |dilFun x t u - dilFun x t v| = |u - v| := by
    rw [hd, abs_neg, abs_div, div_eq_mul_inv]
    calc |t| * (|u - v| * |t|⁻¹) = |u - v| * (|t| * |t|⁻¹) := by ring
      _ = |u - v| * 1 := by rw [mul_inv_cancel₀ (abs_ne_zero.mpr ht)]
      _ = |u - v| := mul_one _
  rw [Real.dist_eq, Real.dist_eq, htv, hmain]

/-- The dilated window `u ↦ Ψ((x-u)/t)` as a Schwartz map. -/
noncomputable def winDil (Ψ : SchwartzMap ℝ ℂ) (x t : ℝ) (ht : t ≠ 0) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz (𝕜 := ℝ) (F := ℂ) (dilFun_temp x t) (dilFun_anti x t ht) Ψ

lemma winDil_apply (Ψ : SchwartzMap ℝ ℂ) (x t : ℝ) (ht : t ≠ 0) (u : ℝ) :
    winDil Ψ x t ht u = Ψ ((x - u)/t) := rfl

lemma memLp_winDil (Ψ : SchwartzMap ℝ ℂ) (x t : ℝ) (ht : t ≠ 0) :
    MemLp (fun u : ℝ => Ψ ((x - u)/t)) 2 (volume : Measure ℝ) := by
  change MemLp (⇑(winDil Ψ x t ht)) 2 (volume : Measure ℝ)
  exact (winDil Ψ x t ht).memLp 2 (volume : Measure ℝ)

/-! ### The dyadic scale, the window `winK`, and the curve -/

/-- The scale `t_j = 2^{j+1} = 1/h_j`. -/
noncomputable def scaleTj (j : ℕ) : ℝ := (2:ℝ)^(j+1)

lemma scaleTj_pos (j : ℕ) : 0 < scaleTj j := by
  unfold scaleTj
  positivity

lemma scaleTj_eq_inv (j : ℕ) : ((2:ℝ)^(-(j:ℝ)-1)) = (scaleTj j)⁻¹ := by
  unfold scaleTj
  rw [show (-(j:ℝ)-1) = -((j:ℝ)+1) by ring, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_natCast]
  congr 1
  push_cast
  ring

/-- The dyadic-scale window `h_j Ψ(h_j ·)`, `h_j = 2^{-(j+1)}`. -/
noncomputable def winK (Ψ : SchwartzMap ℝ ℂ) (j : ℕ) : ℝ → ℂ :=
  fun u => (((2:ℝ)^(-(j:ℝ)-1) : ℝ) : ℂ) * (Ψ ((2:ℝ)^(-(j:ℝ)-1) * u))

lemma winK_eq_smul (Ψ : SchwartzMap ℝ ℂ) (j : ℕ) (u : ℝ) :
    winK Ψ j u = (((scaleTj j : ℝ)⁻¹ : ℝ) : ℂ) * (Ψ (u / scaleTj j)) := by
  unfold winK
  rw [scaleTj_eq_inv]
  congr 1
  rw [div_eq_mul_inv]
  ring

lemma memLp_winK (Ψ : SchwartzMap ℝ ℂ) (j : ℕ) (z : ℝ) :
    MemLp (fun u : ℝ => winK Ψ j (z - u)) 2 (volume : Measure ℝ) := by
  have h := memLp_winDil Ψ z (scaleTj j) (scaleTj_pos j).ne'
  have h2 : MemLp (fun u : ℝ => (((scaleTj j : ℝ)⁻¹ : ℝ) : ℂ) * Ψ ((z - u) / scaleTj j)) 2
      (volume : Measure ℝ) := h.const_mul _
  refine MemLp.ae_eq ?_ h2
  exact Filter.Eventually.of_forall fun u => (winK_eq_smul Ψ j (z - u)).symm

lemma integrable_mul_winK (Ψ : SchwartzMap ℝ ℂ) (j : ℕ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) (x : ℝ) :
    Integrable (fun u : ℝ => g u * winK Ψ j (x - u)) (volume : Measure ℝ) :=
  hg.integrable_mul (memLp_winK Ψ j x)

/-- The windowed convolution (curve point) of `H k` at scale `j`, evaluated at `z`. -/
noncomputable def curvePt (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (j : ℕ) (z : ℝ)
    (k : Fin K) : ℂ :=
  ∫ u : ℝ, H k u * winK Ψ j (z - u)

/-- The curve point with its phase `e^{-I λ_k z}`. -/
noncomputable def curvePtPh (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (j : ℕ) (z : ℝ) (k : Fin K) : ℂ :=
  Complex.exp (-(Complex.I * (lam k : ℂ) * (z : ℂ))) * curvePt Ψ H j z k

/-- The dyadic band operator: `Σ_k e^{-I λ_k x} (H_k * winK_j)(x)`. -/
noncomputable def bandOpD (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (j : ℕ) (x : ℝ) : ℂ :=
  ∑ k : Fin K, curvePtPh Ψ lam H j x k

/-- The `ℓ²` energy of the tuple `H`. -/
noncomputable def bandSq (H : Fin K → ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (∑ k : Fin K, ‖H k x‖ ^ 2)

/-- The maximal function of the band operator over the dyadic scales. -/
noncomputable def bandMax (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x, (⨆ j : ℕ, ‖bandOpD Ψ lam H j x‖ₑ) ^ (2:ℝ)

/-- The translate `T_y H`. -/
noncomputable def transH (H : Fin K → ℝ → ℂ) (y : ℝ) : Fin K → ℝ → ℂ :=
  fun k x => H k (x + y)

/-- The difference `H - T_y H`. -/
noncomputable def shiftH (H : Fin K → ℝ → ℂ) (y : ℝ) : Fin K → ℝ → ℂ :=
  fun k x => H k x - H k (x + y)

/-! ### Elementary algebra of the band operator -/

lemma curvePt_add (Ψ : SchwartzMap ℝ ℂ) (H G : Fin K → ℝ → ℂ) (j : ℕ) (z : ℝ) (k : Fin K)
    (hH : MemLp (H k) 2 (volume : Measure ℝ)) (hG : MemLp (G k) 2 (volume : Measure ℝ)) :
    curvePt Ψ (fun k' x => H k' x + G k' x) j z k = curvePt Ψ H j z k + curvePt Ψ G j z k := by
  unfold curvePt
  rw [← integral_add (integrable_mul_winK Ψ j hH z) (integrable_mul_winK Ψ j hG z)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  ring

lemma curvePt_sub (Ψ : SchwartzMap ℝ ℂ) (H G : Fin K → ℝ → ℂ) (j : ℕ) (z : ℝ) (k : Fin K)
    (hH : MemLp (H k) 2 (volume : Measure ℝ)) (hG : MemLp (G k) 2 (volume : Measure ℝ)) :
    curvePt Ψ (fun k' x => H k' x - G k' x) j z k = curvePt Ψ H j z k - curvePt Ψ G j z k := by
  unfold curvePt
  rw [← integral_sub (integrable_mul_winK Ψ j hH z) (integrable_mul_winK Ψ j hG z)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  ring

lemma bandOp_add (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H G : Fin K → ℝ → ℂ) (j : ℕ)
    (x : ℝ) (hH : ∀ k, MemLp (H k) 2 (volume : Measure ℝ))
    (hG : ∀ k, MemLp (G k) 2 (volume : Measure ℝ)) :
    bandOpD Ψ lam (fun k z => H k z + G k z) j x
      = bandOpD Ψ lam H j x + bandOpD Ψ lam G j x := by
  unfold bandOpD curvePtPh
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [curvePt_add Ψ H G j x k (hH k) (hG k)]
  ring

lemma bandOp_sub (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H G : Fin K → ℝ → ℂ) (j : ℕ)
    (x : ℝ) (hH : ∀ k, MemLp (H k) 2 (volume : Measure ℝ))
    (hG : ∀ k, MemLp (G k) 2 (volume : Measure ℝ)) :
    bandOpD Ψ lam (fun k z => H k z - G k z) j x
      = bandOpD Ψ lam H j x - bandOpD Ψ lam G j x := by
  unfold bandOpD curvePtPh
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [curvePt_sub Ψ H G j x k (hH k) (hG k)]
  ring

/-! ### Measurability -/

/-! ### The triangle inequality for the maximal function -/

/-! ### The `u`-averaging identities -/

lemma curvePt_translate (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (j : ℕ) (z y : ℝ)
    (k : Fin K) (hH : MemLp (H k) 2 (volume : Measure ℝ)) :
    curvePt Ψ (transH H y) j z k = curvePt Ψ H j (z + y) k := by
  have hF : (fun u : ℝ => H k (u + y) * winK Ψ j (z - u))
      = fun u : ℝ => (fun t : ℝ => H k t * winK Ψ j (z + y - t)) (u + y) := by
    funext u
    simp only []
    congr 2
    ring
  unfold curvePt
  simp only [transH]
  rw [hF]
  have key : (∫ u : ℝ, (fun t : ℝ => H k t * winK Ψ j (z + y - t)) (u + y))
      = ∫ u : ℝ, (fun t : ℝ => H k t * winK Ψ j (z + y - t)) u :=
    integral_add_right_eq_self (μ := volume) (f := fun t : ℝ => H k t * winK Ψ j (z + y - t)) y
  rw [key]

lemma bandOpD_translate (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (j : ℕ) (x y : ℝ) (hH : ∀ k, MemLp (H k) 2 (volume : Measure ℝ)) :
    bandOpD Ψ lam (transH H y) j x
      = ∑ k : Fin K, Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))
          * curvePtPh Ψ lam H j (x + y) k := by
  unfold bandOpD
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold curvePtPh
  rw [curvePt_translate Ψ H j x y k (hH k)]
  rw [show -(Complex.I * (lam k : ℂ) * (x : ℂ))
        = Complex.I * (lam k : ℂ) * (y : ℂ)
          + (-(Complex.I * (lam k : ℂ) * ((x + y : ℝ) : ℂ))) by push_cast; ring,
    Complex.exp_add]
  ring

/-- **The `u`-averaging identity** (Krause's reduction): the maximal function of the translate
`T_y H` is the maximal exponential sum with the curve-point coefficients. -/
lemma bandMax_translate (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (hH : ∀ k, MemLp (H k) 2 (volume : Measure ℝ)) (y : ℝ) :
    bandMax Ψ lam (transH H y)
      = ∫⁻ z : ℝ, (⨆ j : ℕ, ‖∑ k : Fin K, Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))
          * curvePtPh Ψ lam H j z k‖ₑ) ^ (2:ℝ) := by
  have hpt : ∀ x : ℝ, (⨆ j : ℕ, ‖bandOpD Ψ lam (transH H y) j x‖ₑ)
      = (⨆ j : ℕ, ‖∑ k : Fin K, Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))
          * curvePtPh Ψ lam H j (x + y) k‖ₑ) := by
    intro x
    refine iSup_congr fun j => ?_
    rw [bandOpD_translate Ψ lam H j x y hH]
  unfold bandMax
  rw [lintegral_congr fun x => congrArg (fun t : ℝ≥0∞ => t ^ (2:ℝ)) (hpt x)]
  exact lintegral_add_right_eq_self (fun z : ℝ => (⨆ j : ℕ, ‖∑ k : Fin K,
      Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) * curvePtPh Ψ lam H j z k‖ₑ) ^ (2:ℝ)) y

/-! ### The band-limited contraction -/

/-! ### The a priori bound -/

/-- The band sum in the form of the published dilation bound. -/
noncomputable def bandSumC (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (t : {t : ℝ // 0 < t}) (x : ℝ) : ℂ :=
  ∑ k : Fin K, Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) *
    (∫ y : ℝ, H k y * (((t : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((t : ℝ)))))

lemma bandOpD_eq_bandSumC (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (j : ℕ) (x : ℝ) :
    bandOpD Ψ lam H j x = bandSumC Ψ lam H ⟨scaleTj j, scaleTj_pos j⟩ x := by
  unfold bandOpD bandSumC curvePtPh curvePt
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only []
  rw [winK_eq_smul]
  simp only [Complex.real_smul]

/-- The maximal function is dominated by the continuous-scale supremum. -/
lemma bandMax_le_continuum (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ) :
    bandMax Ψ lam H ≤ ∫⁻ x, (⨆ (t : {t : ℝ // 0 < t}), ‖bandSumC Ψ lam H t x‖ₑ) ^ (2:ℝ) := by
  refine lintegral_mono fun x => ENNReal.rpow_le_rpow ?_ (by norm_num)
  refine iSup_le fun j => ?_
  rw [bandOpD_eq_bandSumC Ψ lam H j x]
  exact le_iSup (fun t : {t : ℝ // 0 < t} => ‖bandSumC Ψ lam H t x‖ₑ) ⟨scaleTj j, scaleTj_pos j⟩

/-! ### The abstract bootstrap -/

/-- **Bourgain's bootstrap (abstract form).**  Assume for a fixed shift `y`:
* admissibility is preserved by the shift `H ↦ H - T_y H`,
* the one-step inequality `bandMax H ≤ A·bandSq H + bandMax (H - T_yH)`,
* the contraction `bandSq (H - T_yH) ≤ θ²·bandSq H`,
* the a priori bound `bandMax H ≤ CK·bandSq H`.
Then `bandMax H ≤ (A/(1-θ²))·bandSq H` whenever `2θ² < 1`. -/
theorem bandMax_le_of_oneStep (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (y : ℝ) {A θ CK : ℝ}
    (hA : 0 ≤ A) (hApos : 0 < A) (hθ0 : 0 ≤ θ) (hθ : 2 * θ ^ 2 < 1) (hCK : 0 ≤ CK)
    (Adm : (Fin K → ℝ → ℂ) → Prop)
    (hpres : ∀ H, Adm H → Adm (shiftH H y))
    (hone : ∀ H, Adm H →
      bandMax Ψ lam H ≤ ENNReal.ofReal A * bandSq H + bandMax Ψ lam (shiftH H y))
    (hcon : ∀ H, Adm H → bandSq (shiftH H y) ≤ ENNReal.ofReal (θ ^ 2) * bandSq H)
    (hap : ∀ H, Adm H → bandMax Ψ lam H ≤ ENNReal.ofReal CK * bandSq H)
    (H : Fin K → ℝ → ℂ) (hH : Adm H) :
    bandMax Ψ lam H ≤ ENNReal.ofReal (A / (1 - θ ^ 2)) * bandSq H := by
  set Hn : ℕ → Fin K → ℝ → ℂ := fun n => Nat.rec H (fun n G => shiftH G y) n with hHn
  have hHn_succ : ∀ n, Hn (n+1) = shiftH (Hn n) y := fun n => rfl
  have hAdm : ∀ n, Adm (Hn n) := by
    intro n
    induction n with
    | zero => exact hH
    | succ n ih => rw [hHn_succ n]; exact hpres (Hn n) ih
  have hrec : ∀ n, bandMax Ψ lam (Hn n) ≤
      ENNReal.ofReal A * bandSq (Hn n) + bandMax Ψ lam (Hn (n+1)) := by
    intro n
    have := hone (Hn n) (hAdm n)
    rw [← hHn_succ n] at this
    exact this
  have hsq : ∀ n, bandSq (Hn (n+1)) ≤ ENNReal.ofReal (θ ^ 2) * bandSq (Hn n) := by
    intro n
    have := hcon (Hn n) (hAdm n)
    rw [← hHn_succ n] at this
    exact this
  have hsq_pow : ∀ n, bandSq (Hn n) ≤ (ENNReal.ofReal (θ ^ 2)) ^ n * bandSq H := by
    intro n
    induction n with
    | zero => simp [hHn]
    | succ n ih =>
        calc bandSq (Hn (n+1)) ≤ ENNReal.ofReal (θ^2) * bandSq (Hn n) := hsq n
          _ ≤ ENNReal.ofReal (θ^2) * ((ENNReal.ofReal (θ^2)) ^ n * bandSq H) :=
              mul_le_mul_of_nonneg_left ih (bot_le)
          _ = (ENNReal.ofReal (θ^2)) ^ (n+1) * bandSq H := by ring
  have htot : ∀ n, bandMax Ψ lam H
      ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) * bandSq H
        + bandMax Ψ lam (Hn n) := by
    intro n
    induction n with
    | zero => simp [hHn]
    | succ n ih =>
        calc bandMax Ψ lam H
            ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) * bandSq H
              + bandMax Ψ lam (Hn n) := ih
          _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) * bandSq H
              + (ENNReal.ofReal A * bandSq (Hn n) + bandMax Ψ lam (Hn (n+1))) :=
              add_le_add (le_refl _) (hrec n)
          _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) * bandSq H
              + (ENNReal.ofReal A * ((ENNReal.ofReal (θ^2)) ^ n * bandSq H)
                + bandMax Ψ lam (Hn (n+1))) := by
              refine add_le_add (le_refl _) (add_le_add ?_ (le_refl _))
              exact mul_le_mul_of_nonneg_left (hsq_pow n) (bot_le)
          _ = (∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) * bandSq H
              + bandMax Ψ lam (Hn (n+1)) := by
              rw [Finset.sum_range_succ]; ring
  have htail : ∀ n, bandMax Ψ lam (Hn n) ≤ ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n
      * bandSq H := by
    intro n
    calc bandMax Ψ lam (Hn n) ≤ ENNReal.ofReal CK * bandSq (Hn n) := hap (Hn n) (hAdm n)
      _ ≤ ENNReal.ofReal CK * ((ENNReal.ofReal (θ^2)) ^ n * bandSq H) :=
          mul_le_mul_of_nonneg_left (hsq_pow n) (bot_le)
      _ = ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n * bandSq H := by ring
  have hfin : bandMax Ψ lam H ≤ ⨅ n, ((∑ i ∈ Finset.range n,
      ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n)
      * bandSq H := by
    refine le_iInf (fun n => ?_)
    calc bandMax Ψ lam H
        ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) * bandSq H
          + bandMax Ψ lam (Hn n) := htot n
      _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) * bandSq H
          + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n * bandSq H := add_le_add (le_refl _) (htail n)
      _ = ((∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
            + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n) * bandSq H := by ring
  have hcast1 : ∀ n, (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
      = ENNReal.ofReal (A * (∑ i ∈ Finset.range n, (θ^2) ^ i)) := by
    intro n
    have hterm : ∀ i, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i
        = ENNReal.ofReal (A * (θ^2)^i) := by
      intro i
      rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_pow (sq_nonneg θ)]
    rw [Finset.sum_congr rfl (fun i _ => hterm i),
      ← ENNReal.ofReal_sum_of_nonneg
        (fun i _ => mul_nonneg hA (pow_nonneg (sq_nonneg θ) i))]
    conv_rhs => rw [Finset.mul_sum]
  have hcast2 : ∀ n, ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n
      = ENNReal.ofReal (CK * (θ^2) ^ n) := by
    intro n
    rw [ENNReal.ofReal_mul hCK, ENNReal.ofReal_pow (sq_nonneg θ)]
  have hcast : ∀ n, ((∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n)
      = ENNReal.ofReal (A * (∑ i ∈ Finset.range n, (θ^2) ^ i) + CK * (θ^2) ^ n) := by
    intro n
    rw [hcast1 n, hcast2 n, ← ENNReal.ofReal_add
      (mul_nonneg hA (Finset.sum_nonneg fun i _ => pow_nonneg (sq_nonneg θ) i))
      (mul_nonneg hCK (pow_nonneg (sq_nonneg θ) _))]
  have hgeo : ∀ n, (∑ i ∈ Finset.range n, (θ^2)^i) ≤ (1 - θ^2)⁻¹ := by
    intro n
    have hden : 0 < 1 - θ^2 := by nlinarith
    rw [inv_eq_one_div, le_div_iff₀ hden]
    have hgm := geom_sum_mul (θ^2) n
    have h1 : (∑ i ∈ Finset.range n, (θ^2)^i) * (1 - θ^2) = 1 - (θ^2)^n := by
      have := geom_sum_mul (θ^2) n
      rw [show (1:ℝ) - θ^2 = -((θ^2) - 1) by ring, mul_neg, this]
      ring
    rw [h1]
    have : (0:ℝ) ≤ (θ^2)^n := pow_nonneg (sq_nonneg θ) n
    linarith
  have hlim : (⨅ n, ((∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n)) ≤ ENNReal.ofReal (A / (1 - θ^2)) := by
    refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
    have hlt : (θ^2) < 1 := by nlinarith
    obtain ⟨n, hn⟩ : ∃ n : ℕ, CK * (θ^2)^n ≤ (ε : ℝ) := by
      rcases eq_or_lt_of_le hCK with h0 | hpos
      · refine ⟨0, ?_⟩
        rw [← h0]; simp
      · have hε' : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
        obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ) < (ε:ℝ)/CK) hlt
        refine ⟨n, le_of_lt ?_⟩
        calc CK * (θ^2)^n < CK * ((ε:ℝ)/CK) := mul_lt_mul_of_pos_left hn hpos
          _ = (ε:ℝ) := by field_simp
    calc (⨅ n, ((∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
            + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n))
        ≤ ((∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
            + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n) := iInf_le _ n
      _ = ENNReal.ofReal (A * (∑ i ∈ Finset.range n, (θ^2) ^ i) + CK * (θ^2) ^ n) := hcast n
      _ ≤ ENNReal.ofReal (A * (1 - θ^2)⁻¹ + (ε : ℝ)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hge := hgeo n
          have hA1 : A * (∑ i ∈ Finset.range n, (θ^2)^i) ≤ A * (1 - θ^2)⁻¹ :=
            mul_le_mul_of_nonneg_left hge hA
          linarith [hn]
      _ = ENNReal.ofReal (A * (1 - θ^2)⁻¹) + ENNReal.ofReal ((ε : ℝ)) :=
          ENNReal.ofReal_add (by positivity) (by positivity)
      _ = ENNReal.ofReal (A / (1 - θ^2)) + (ε : ENNReal) := by
          rw [ENNReal.ofReal_coe_nnreal]
          congr 1
  have hX1 : ∀ n : ℕ, ENNReal.ofReal A ≤ (∑ i ∈ Finset.range (n+1),
      ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1) := by
    intro n
    have h1 : ENNReal.ofReal A ≤ ∑ i ∈ Finset.range (n+1),
        ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i := by
      have := Finset.single_le_sum
        (f := fun i => ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
        (fun i _ => bot_le) (Finset.mem_range.mpr (Nat.succ_pos n))
      simpa using this
    exact le_add_right h1
  have hLpos : 0 < ⨅ n, ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1)) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hApos) (le_iInf fun n => hX1 n)
  have hLtop : (⨅ n, ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1))) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (iInf_le _ 0) ?_)
    rw [hcast (0+1)]
    simp only [Nat.zero_add]
    exact ENNReal.ofReal_lt_top
  have hfin : bandMax Ψ lam H ≤ ⨅ n, ((∑ i ∈ Finset.range (n+1),
      ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1)) * bandSq H := by
    refine le_iInf fun n => ?_
    calc bandMax Ψ lam H
        ≤ (∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) * bandSq H
          + bandMax Ψ lam (Hn (n+1)) := htot (n+1)
      _ ≤ (∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) * bandSq H
          + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1) * bandSq H :=
          add_le_add (le_refl _) (htail (n+1))
      _ = ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
            + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1)) * bandSq H := by ring
  have hkey : ∀ ε : NNReal, 0 < ε → ∃ n : ℕ, ((∑ i ∈ Finset.range (n+1),
      ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1))
      ≤ ENNReal.ofReal (A / (1 - θ^2)) + (ε : ENNReal) := by
    intro ε hε
    have hlt : (θ^2) < 1 := by nlinarith
    have hε' : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
    obtain ⟨n, hn⟩ : ∃ n : ℕ, CK * (θ^2)^(n+1) ≤ (ε : ℝ) := by
      rcases eq_or_lt_of_le hCK with h0 | hpos
      · refine ⟨0, ?_⟩
        rw [← h0, zero_mul]
        exact hε'.le
      · obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ) < (ε:ℝ)/CK) hlt
        refine ⟨m, le_of_lt ?_⟩
        calc CK * (θ^2)^(m+1) = (CK * (θ^2)^m) * (θ^2) := by ring
          _ ≤ (CK * (θ^2)^m) * 1 :=
              mul_le_mul_of_nonneg_left hlt.le (by positivity)
          _ = CK * (θ^2)^m := by ring
          _ < CK * ((ε:ℝ)/CK) := mul_lt_mul_of_pos_left hm hpos
          _ = (ε:ℝ) := by field_simp
    refine ⟨n, ?_⟩
    calc ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
          + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1))
        = ENNReal.ofReal (A * (∑ i ∈ Finset.range (n+1), (θ^2) ^ i) + CK * (θ^2) ^ (n+1)) :=
          hcast (n+1)
      _ ≤ ENNReal.ofReal (A * (1 - θ^2)⁻¹ + (ε : ℝ)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hge := hgeo (n+1)
          have hA1 : A * (∑ i ∈ Finset.range (n+1), (θ^2)^i) ≤ A * (1 - θ^2)⁻¹ :=
            mul_le_mul_of_nonneg_left hge hA
          linarith [hn]
      _ = ENNReal.ofReal (A * (1 - θ^2)⁻¹) + ENNReal.ofReal ((ε : ℝ)) :=
          ENNReal.ofReal_add (by positivity) (by positivity)
      _ = ENNReal.ofReal (A / (1 - θ^2)) + (ε : ENNReal) := by
          rw [ENNReal.ofReal_coe_nnreal]
          congr 1
  have hlimShift : (⨅ n, ((∑ i ∈ Finset.range (n+1),
      ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1))) ≤ ENNReal.ofReal (A / (1 - θ^2)) := by
    refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
    obtain ⟨n, hn⟩ := hkey ε hε
    exact (iInf_le _ n).trans hn
  calc bandMax Ψ lam H
      ≤ ⨅ n, ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
          + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1)) * bandSq H := hfin
    _ = (⨅ n, ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
          + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1))) * bandSq H :=
        (ENNReal.iInf_mul (f := fun n => (∑ i ∈ Finset.range (n+1),
            ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
            + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1))
          (a := bandSq H) (fun _ h0 => absurd h0 hLpos.ne')).symm
    _ ≤ ENNReal.ofReal (A / (1 - θ^2)) * bandSq H :=
        mul_le_mul_of_nonneg_right hlimShift bot_le

end

end Commons.Analysis.Fourier


/-!
# The entropy step of Bourgain's Lemma 4.13

The `u`-averaging identity `bandMax_translate` turns the maximal function of a translate into a
maximal exponential sum with the curve coefficients.  This file develops the chaining argument
which bounds it: the net construction (`exists_net_selfmap_l2`), the per-`z` chain bound, and the
comparison of the resulting dyadic sum with the entropy integral (`winML2`), which is bounded by
`bourgain_entropy_integral_l2_l2vec`.
-/

namespace Commons.Analysis.Fourier

open _root_.MeasureTheory Finset Function Filter
open scoped _root_.ENNReal _root_.Topology BigOperators

noncomputable section

variable {K : ℕ}

/-! ### The entropy chain on an arbitrary unit interval -/

/-- `∫⁻ y in (0,1], F (y + c) = ∫⁻ y in (c, c+1], F y`. -/
private lemma lintegral_Ioc_add_right (F : ℝ → ℝ≥0∞) (c : ℝ) :
    ∫⁻ y in Set.Ioc (0:ℝ) 1, F (y + c) = ∫⁻ y in Set.Ioc c (c + 1), F y := by
  rw [← MeasureTheory.lintegral_indicator measurableSet_Ioc,
      ← MeasureTheory.lintegral_indicator measurableSet_Ioc]
  have h1 : ∀ y, Set.indicator (Set.Ioc (0:ℝ) 1) (fun z => F (z + c)) y
      = Set.indicator (Set.Ioc c (c + 1)) F (y + c) := by
    intro y
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : y ∈ Set.Ioc (0:ℝ) 1
    · rw [if_pos h, if_pos ⟨by linarith [h.1], by linarith [h.2]⟩]
    · rw [if_neg h]
      by_cases h2 : y + c ∈ Set.Ioc c (c + 1)
      · exact absurd ⟨by linarith [h2.1], by linarith [h2.2]⟩ h
      · rw [if_neg h2]
  calc ∫⁻ y, Set.indicator (Set.Ioc (0:ℝ) 1) (fun z => F (z + c)) y
      = ∫⁻ y, Set.indicator (Set.Ioc c (c + 1)) F (y + c) := by simp only [h1]
    _ = ∫⁻ y, Set.indicator (Set.Ioc c (c + 1)) F y :=
        MeasureTheory.lintegral_add_right_eq_self _ c

/-- The character `y ↦ e^{I λ y}` has modulus one. -/
private lemma norm_cexp_lin (lam y : ℝ) :
    ‖Complex.exp (Complex.I * (lam : ℂ) * (y : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (Complex.I * (lam : ℂ) * (y : ℂ)).re = 0 := by
    rw [Complex.mul_re, Complex.mul_re]; simp
  rw [h, Real.exp_zero]

/-! ### Covers from covering numbers -/

/-- A finite cover of cardinality at most the covering number. -/
lemma exists_cover_of_coveringNumber {X : Type*} [PseudoMetricSpace X] (A : Set X) {ε : NNReal}
    (hfin : Metric.coveringNumber ε A ≠ ⊤) :
    ∃ S : Finset X, (∀ x ∈ A, ∃ s ∈ S, dist x s ≤ ε) ∧
      ((S.card : ℕ∞) ≤ Metric.coveringNumber ε A) := by
  have hIsCov := Metric.isCover_minimalCover (A := A) (ε := ε) hfin
  have hfin' : (Metric.minimalCover ε A).Finite := Metric.finite_minimalCover
  refine ⟨hfin'.toFinset, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hIsCov hx
    refine ⟨y, hfin'.mem_toFinset.mpr hy, ?_⟩
    have hxy' : edist x y ≤ (ε : ℝ≥0∞) := by simpa only [Set.mem_setOf_eq] using hxy
    have h1 : (nndist x y : ℝ≥0∞) ≤ (ε : ℝ≥0∞) := by
      rwa [edist_nndist] at hxy'
    have h2 : nndist x y ≤ ε := ENNReal.coe_le_coe.mp h1
    have h3 : dist x y ≤ (ε : ℝ) := by rw [dist_nndist]; exact_mod_cast h2
    exact h3
  · have h1 : ((hfin'.toFinset.card : ℕ) : ℕ∞) = Metric.coveringNumber ε A := by
      rw [← hfin'.encard_eq_coe_toFinset_card, Metric.encard_minimalCover hfin]
    exact le_of_eq h1

/-! ### The dyadic curve family -/

/-- The family of dyadic curve points, as `ℓ²`-vectors. -/
noncomputable def curveVec (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) :
    Fin (S+1) → EuclideanSpace ℂ (Fin K) :=
  fun i => winCurveL2 Ψ H z ⟨scaleTj (i:ℕ), scaleTj_pos (i:ℕ)⟩

lemma curveVec_apply (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ)
    (i : Fin (S+1)) (k : Fin K) :
    curveVec Ψ H S z i k
      = ∫ y : ℝ, H k y * (((scaleTj (i:ℕ) : ℝ)⁻¹ : ℝ) • (Ψ : ℝ → ℂ) ((z - y) / (scaleTj (i:ℕ) : ℝ))) :=
  rfl

/-- The maximal `ℓ²`-norm of the dyadic curve family. -/
noncomputable def curveRad (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖

lemma curveRad_nonneg (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) :
    0 ≤ curveRad Ψ H S z := by
  unfold curveRad
  exact le_trans (norm_nonneg _) (Finset.le_sup' (f := fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖)
    (Finset.mem_univ 0))


/-! ### Dyadic Riemann sums on a scaled grid -/

/-- **Dyadic sum versus integral on the scaled grid `{c·2^{-ℓ}}`.**  For non-increasing
`f : ℝ → ℝ≥0∞` and `c > 0`, `∑_{ℓ<L} 2^{-ℓ} f (c·2^{-ℓ}) ≤ c⁻¹ · 2∫_{(0,c]} f`. -/


lemma enn_min_rpow_half (a b : ℝ≥0∞) :
    (min a b) ^ ((1:ℝ)/2) = min (a ^ ((1:ℝ)/2)) (b ^ ((1:ℝ)/2)) := by
  refine le_antisymm ?_ ?_
  · exact le_min (ENNReal.rpow_le_rpow (min_le_left _ _) (by norm_num))
      (ENNReal.rpow_le_rpow (min_le_right _ _) (by norm_num))
  · rcases le_total a b with h | h
    · rw [min_eq_left h]; exact min_le_left _ _
    · rw [min_eq_right h]; exact min_le_right _ _

private lemma min_add_le (a x y : ℝ≥0∞) : min a (x + y) ≤ min a x + y := by
  rcases le_total a x with h' | h'
  · calc min a (x + y) ≤ a := min_le_left _ _
      _ = min a x := (min_eq_left h').symm
      _ ≤ min a x + y := le_add_right le_rfl
  · calc min a (x + y) ≤ x + y := min_le_right _ _
      _ = min a x + y := by rw [min_eq_right h']

lemma dyadic_sum_le_lintegral_entropy (E : ℝ → ℝ≥0∞)
    (hanti : ∀ r r' : ℝ, 0 < r → r ≤ r' → E r' ≤ E r)
    (hE1 : ∀ r : ℝ, 0 < r → 1 ≤ E r)
    (K : ℕ) (M : ℕ → ℕ) {c : ℝ} (hc : 0 < c) (L : ℕ)
    (hM : ∀ t : ℕ, (M t : ℝ≥0∞) ≤ E (c * (1/2:ℝ)^t)) :
    ENNReal.ofReal (∑ t ∈ Finset.range L,
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      ≤ ENNReal.ofReal c⁻¹ * (2 * (∫⁻ r in Set.Ioi (0:ℝ),
          min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((E r - 1) ^ ((1:ℝ)/2)))) + 4 := by
  set g : ℝ → ℝ≥0∞ := fun r =>
    min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((E r - 1) ^ ((1:ℝ)/2)) with hg
  have hganti : ∀ r r' : ℝ, 0 < r → r ≤ r' → g r' ≤ g r := by
    intro r r' hr hrr
    refine min_le_min le_rfl ?_
    exact ENNReal.rpow_le_rpow (tsub_le_tsub_right (hanti r r' hr hrr) 1) (by norm_num)
  have hbase : ∀ t : ℕ, ENNReal.ofReal (Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      = (min (ENNReal.ofReal (K:ℝ)) ((M t : ℝ≥0∞) + 1)) ^ ((1:ℝ)/2) := by
    intro t
    rw [Real.sqrt_eq_rpow,
      ← ENNReal.ofReal_rpow_of_nonneg (le_min (Nat.cast_nonneg K) (by positivity))
        (by norm_num : (0:ℝ) ≤ (1:ℝ)/2),
      ENNReal.ofReal_min, ENNReal.ofReal_add (by positivity) (by norm_num),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    simp only [ENNReal.ofReal_natCast]
  have hK : (ENNReal.ofReal (K:ℝ)) ^ ((1:ℝ)/2) = ENNReal.ofReal (Real.sqrt (K:ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg K)
      (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)]
  have hterm : ∀ t : ℕ, ENNReal.ofReal ((1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      ≤ ENNReal.ofReal ((1/2:ℝ)^t) * (g (c * (1/2:ℝ)^t) + 2) := by
    intro t
    have hstep : ENNReal.ofReal (Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
        ≤ g (c * (1/2:ℝ)^t) + 2 := by
      rw [hbase, enn_min_rpow_half, hK]
      refine le_trans (min_le_min le_rfl ?_) (min_add_le _ _ 2)
      calc ((M t : ℝ≥0∞) + 1) ^ ((1:ℝ)/2)
          ≤ (E (c * (1/2:ℝ)^t) + 1) ^ ((1:ℝ)/2) :=
            ENNReal.rpow_le_rpow (add_le_add (hM t) le_rfl) (by norm_num)
        _ ≤ ((E (c * (1/2:ℝ)^t) - 1) + 2) ^ ((1:ℝ)/2) := by
            apply ENNReal.rpow_le_rpow _ (by norm_num)
            have h1 : E (c * (1/2:ℝ)^t) ≤ E (c * (1/2:ℝ)^t) - 1 + 1 := by
              rw [tsub_add_cancel_of_le (hE1 _ (by positivity))]
            calc E (c * (1/2:ℝ)^t) + 1
                ≤ (E (c * (1/2:ℝ)^t) - 1 + 1) + 1 := add_le_add h1 le_rfl
              _ = (E (c * (1/2:ℝ)^t) - 1) + 2 := by ring
        _ ≤ (E (c * (1/2:ℝ)^t) - 1) ^ ((1:ℝ)/2) + 2 ^ ((1:ℝ)/2) :=
            ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)
        _ ≤ (E (c * (1/2:ℝ)^t) - 1) ^ ((1:ℝ)/2) + 2 := by
            refine add_le_add le_rfl ?_
            have h := ENNReal.rpow_le_rpow_of_exponent_le
              (show (1:ℝ≥0∞) ≤ 2 by norm_num) (show ((1:ℝ)/2) ≤ 1 by norm_num)
            simpa using h
    rw [ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul le_rfl hstep bot_le bot_le
  have hsum : ENNReal.ofReal (∑ t ∈ Finset.range L,
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      = ∑ t ∈ Finset.range L, ENNReal.ofReal
          ((1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1))) :=
    ENNReal.ofReal_sum_of_nonneg (fun t _ => by positivity)
  rw [hsum]
  have hsplit : ∑ t ∈ Finset.range L, ENNReal.ofReal
        ((1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      ≤ (∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * g (c * (1/2:ℝ)^t))
        + ∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * 2 := by
    calc ∑ t ∈ Finset.range L, ENNReal.ofReal
          ((1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
        ≤ ∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * (g (c * (1/2:ℝ)^t) + 2) :=
          Finset.sum_le_sum (fun t _ => hterm t)
      _ = (∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * g (c * (1/2:ℝ)^t))
          + ∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * 2 := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun t _ => by ring
  have hgeo : ∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * 2 ≤ 4 := by
    have h1 : ∑ t ∈ Finset.range L, (1/2:ℝ)^t ≤ 2 := by
      have h2 : ∑ t ∈ Finset.range L, (1/2:ℝ)^t = 2 * (1 - (1/2:ℝ)^L) := by
        rw [geom_sum_eq (by norm_num : (1/2:ℝ) ≠ 1)]
        field_simp
        ring
      rw [h2]
      have : (0:ℝ) < (1/2:ℝ)^L := pow_pos (by norm_num : (0:ℝ) < 1/2) _
      linarith
    calc ∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * 2
        = (∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t)) * 2 :=
            (Finset.sum_mul _ _ _).symm
      _ = ENNReal.ofReal (∑ t ∈ Finset.range L, (1/2:ℝ)^t) * 2 := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => by positivity)]
      _ ≤ ENNReal.ofReal 2 * 2 :=
          mul_le_mul (ENNReal.ofReal_le_ofReal h1) le_rfl bot_le bot_le
      _ = 4 := by norm_num
  have hmain : ∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * g (c * (1/2:ℝ)^t)
      ≤ ENNReal.ofReal c⁻¹ * (2 * (∫⁻ r in Set.Ioi (0:ℝ), g r)) := by
    let d : ℕ → Set ℝ := fun t => Set.Ioc (c * (1/2:ℝ)^(t+1)) (c * (1/2:ℝ)^t)
    have hclen : ∀ t, ENNReal.ofReal ((1/2:ℝ)^t)
        = ENNReal.ofReal c⁻¹ * (2 * volume (d t)) := by
      intro t
      have hvol : volume (d t) = ENNReal.ofReal (c * (1/2:ℝ)^(t+1)) := by
        rw [Real.volume_Ioc]; congr 1; ring
      rw [hvol, show (2:ℝ≥0∞) = ENNReal.ofReal 2 by simp,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
      congr 1
      rw [pow_succ]
      field_simp
    have hcdisj : (Finset.range L : Set ℕ).PairwiseDisjoint d := by
      intro i hi j hj hij
      change Disjoint (d i) (d j)
      rw [Set.disjoint_left]
      intro r hri hrj
      have hri' : r ∈ Set.Ioc (c * (1/2:ℝ)^(i+1)) (c * (1/2:ℝ)^i) := hri
      have hrj' : r ∈ Set.Ioc (c * (1/2:ℝ)^(j+1)) (c * (1/2:ℝ)^j) := hrj
      simp only [Set.mem_Ioc] at hri' hrj'
      rcases lt_or_gt_of_ne hij with h | h
      · have hle : c * (1/2:ℝ)^j ≤ c * (1/2:ℝ)^(i+1) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hc.le
        linarith [hri'.1, hrj'.2, hle]
      · have hle : c * (1/2:ℝ)^i ≤ c * (1/2:ℝ)^(j+1) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hc.le
        linarith [hrj'.1, hri'.2, hle]
    have hterm2 : ∀ t, ENNReal.ofReal ((1/2:ℝ)^t) * g (c * (1/2:ℝ)^t)
        ≤ ENNReal.ofReal c⁻¹ * (2 * ∫⁻ r in d t, g r) := by
      intro t
      have hmono : ∫⁻ r in d t, g (c * (1/2:ℝ)^t) ≤ ∫⁻ r in d t, g r := by
        apply setLIntegral_mono' (μ := volume) measurableSet_Ioc
        intro r hr
        have hr' : r ∈ Set.Ioc (c * (1/2:ℝ)^(t+1)) (c * (1/2:ℝ)^t) := hr
        simp only [Set.mem_Ioc] at hr'
        exact hganti r (c * (1/2:ℝ)^t)
          (by linarith [hr'.1, mul_pos hc (pow_pos (by norm_num : (0:ℝ) < 1/2) (t+1))]) hr'.2
      calc ENNReal.ofReal ((1/2:ℝ)^t) * g (c * (1/2:ℝ)^t)
          = ENNReal.ofReal c⁻¹ * (2 * (volume (d t) * g (c * (1/2:ℝ)^t))) := by
            rw [hclen t]; ring_nf
        _ = ENNReal.ofReal c⁻¹ * (2 * ∫⁻ r in d t, g (c * (1/2:ℝ)^t)) := by
            rw [setLIntegral_const (μ := volume) (d t) (g (c * (1/2:ℝ)^t)),
              mul_comm (g (c * (1/2:ℝ)^t)) (volume (d t))]
        _ ≤ ENNReal.ofReal c⁻¹ * (2 * ∫⁻ r in d t, g r) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono (by norm_num)) bot_le
    calc ∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * g (c * (1/2:ℝ)^t)
        ≤ ∑ t ∈ Finset.range L, ENNReal.ofReal c⁻¹ * (2 * ∫⁻ r in d t, g r) :=
          Finset.sum_le_sum (fun t _ => hterm2 t)
      _ = ENNReal.ofReal c⁻¹ * (2 * ∑ t ∈ Finset.range L, ∫⁻ r in d t, g r) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ = ENNReal.ofReal c⁻¹ * (2 * ∫⁻ r in (⋃ t ∈ Finset.range L, d t), g r) := by
          rw [MeasureTheory.lintegral_biUnion_finset hcdisj (fun t _ => measurableSet_Ioc) g]
      _ ≤ ENNReal.ofReal c⁻¹ * (2 * (∫⁻ r in Set.Ioi (0:ℝ), g r)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (lintegral_mono_set ?_)
            (by norm_num)) bot_le
          intro r hr
          simp only [Set.mem_iUnion] at hr
          obtain ⟨t, -, ht⟩ := hr
          have ht' : r ∈ Set.Ioc (c * (1/2:ℝ)^(t+1)) (c * (1/2:ℝ)^t) := ht
          simp only [Set.mem_Ioc] at ht'
          show (0:ℝ) < r
          have hpos : (0:ℝ) < (1/2:ℝ)^(t+1) := pow_pos (by norm_num : (0:ℝ) < 1/2) (t+1)
          linarith [ht'.1, mul_pos hc hpos]
  calc ∑ t ∈ Finset.range L, ENNReal.ofReal
        ((1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      ≤ (∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * g (c * (1/2:ℝ)^t))
        + ∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * 2 := hsplit
    _ ≤ ENNReal.ofReal c⁻¹ * (2 * (∫⁻ r in Set.Ioi (0:ℝ), g r)) + 4 := add_le_add hmain hgeo
    _ = ENNReal.ofReal c⁻¹ * (2 * (∫⁻ r in Set.Ioi (0:ℝ),
          min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((E r - 1) ^ ((1:ℝ)/2)))) + 4 := by rw [hg]




lemma curveVec_eq_curvePt (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ)
    (i : Fin (S+1)) (k : Fin K) :
    curveVec Ψ H S z i k = curvePt Ψ H (i:ℕ) z k := by
  simp only [curveVec_apply, curvePt, winK_eq_smul, Complex.real_smul]

lemma euclid_norm_sq (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ)
    (i : Fin (S+1)) :
    ‖curveVec Ψ H S z i‖ ^ 2 = ∑ k : Fin K, ‖curvePt Ψ H (i:ℕ) z k‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun k _ => by positivity)]
  exact Finset.sum_congr rfl fun k _ => by rw [curveVec_eq_curvePt]

/-- Each `ℓ²` norm of the dyadic curve is bounded by `curveRad`. -/
lemma norm_curveVec_le_curveRad (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ)
    (i : Fin (S+1)) : ‖curveVec Ψ H S z i‖ ≤ curveRad Ψ H S z :=
  Finset.le_sup' (f := fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖) (Finset.mem_univ i)

lemma sum_norm_sq_curvePt_le (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ)
    (i : Fin (S+1)) :
    ∑ k : Fin K, ‖curvePt Ψ H (i:ℕ) z k‖ ^ 2 ≤ (curveRad Ψ H S z) ^ 2 := by
  rw [← euclid_norm_sq Ψ H S z i]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_curveVec_le_curveRad Ψ H S z i) 2


end

end Commons.Analysis.Fourier


open _root_.MeasureTheory Finset
open scoped BigOperators _root_.ENNReal _root_.Topology

namespace Commons.Analysis.Fourier

noncomputable section

variable {K : ℕ}

/-- `1 ≤ a + 1` in `ℝ≥0∞`. -/
private lemma one_le_add_one (a : ENNReal) : 1 ≤ a + 1 := by
  calc (1:ENNReal) = 0 + 1 := by simp
    _ ≤ a + 1 := add_le_add bot_le le_rfl

/-- The last dyadic term of the entropy sum is at most one. -/
private lemma dyadic_tail_le_one (K S : ℕ) :
    (1/2:ℝ)^(S+1) * Real.sqrt (min (K:ℝ) ((S:ℝ) + 3)) ≤ 1 := by
  have h4 : ∀ S : ℕ, S + 3 ≤ 4^(S+1) := by
    intro S
    induction S with
    | zero => norm_num
    | succ k ih =>
        have hstep : k + 1 + 3 ≤ 4 * (k + 3) := by omega
        calc k + 1 + 3 ≤ 4 * (k + 3) := hstep
          _ ≤ 4 * 4^(k+1) := Nat.mul_le_mul_left 4 ih
          _ = 4^(k+2) := by ring
  have hsqrt : Real.sqrt (min (K:ℝ) ((S:ℝ) + 3)) ≤ 2^(S+1) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h5 : min (K:ℝ) ((S:ℝ) + 3) ≤ (S:ℝ) + 3 := min_le_right _ _
    have h6 : ((S:ℝ) + 3) ≤ (4:ℝ)^(S+1) := by exact_mod_cast h4 S
    have h7 : ((4:ℝ)^(S+1)) = (2:ℝ)^(S+1) * 2^(S+1) := by
      have : (4:ℝ) = 2 * 2 := by norm_num
      rw [this, mul_pow]
    rw [sq]
    linarith [h5, h6, h7]
  calc (1/2:ℝ)^(S+1) * Real.sqrt (min (K:ℝ) ((S:ℝ) + 3))
      ≤ (1/2:ℝ)^(S+1) * 2^(S+1) := mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = 1 := by rw [← mul_pow]; norm_num

end

end Commons.Analysis.Fourier

open scoped _root_.ENNReal
open _root_.MeasureTheory

namespace Commons.Analysis.Measure

/-- From an integrable bound on an interval, one point where the value is small. -/
theorem exists_le_of_lintegral_le (F : ℝ → ENNReal) (hF : Measurable F)
    {a b : ℝ} (hab : a < b) {K : ENNReal}
    (hint : ∫⁻ x in Set.Ioo a b, F x ∂(volume : Measure ℝ) ≤ K) (hKtop : K ≠ ⊤) :
    ∃ y ∈ Set.Ioo a b, ENNReal.ofReal (b - a) * F y ≤ (K + K) := by
  by_contra h
  push_neg at h
  have hvol : (volume : Measure ℝ) (Set.Ioo a b) = ENNReal.ofReal (b - a) := Real.volume_Ioo
  have hvolne0 : (volume : Measure ℝ) (Set.Ioo a b) ≠ 0 := by
    rw [hvol]; exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hvollt : (volume : Measure ℝ) (Set.Ioo a b) ≠ ⊤ := by
    rw [hvol]; exact ENNReal.ofReal_ne_top
  have hlow : (volume : Measure ℝ) (Set.Ioo a b) * ((K + K) / (volume (Set.Ioo a b)))
      ≤ ∫⁻ x in Set.Ioo a b, F x ∂(volume : Measure ℝ) := by
    calc (volume : Measure ℝ) (Set.Ioo a b) * ((K + K) / (volume (Set.Ioo a b)))
        = ∫⁻ x in Set.Ioo a b, (K + K) / (volume (Set.Ioo a b)) ∂(volume : Measure ℝ) :=
          (by rw [MeasureTheory.setLIntegral_const (μ := volume) (Set.Ioo a b)
              ((K + K) / (volume (Set.Ioo a b))), mul_comm])
      _ ≤ ∫⁻ x in Set.Ioo a b, F x ∂(volume : Measure ℝ) := by
          refine setLIntegral_mono' measurableSet_Ioo fun y hy => ?_
          rw [ENNReal.div_le_iff_le_mul (Or.inl hvolne0) (Or.inl hvollt)]
          rw [mul_comm]
          exact le_of_lt (by simpa only [hvol, mul_comm] using h y hy)
  have hK2 : K + K ≤ K := by
    refine le_trans ?_ hint
    calc K + K = (volume : Measure ℝ) (Set.Ioo a b) * ((K + K) / (volume (Set.Ioo a b))) :=
          (ENNReal.mul_div_cancel hvolne0 hvollt).symm
      _ ≤ _ := hlow
  have hK0 : K = 0 := by
    by_contra h0
    exact absurd hK2 (not_le.mpr (ENNReal.lt_add_right hKtop h0))
  subst hK0
  have hF0 : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Set.Ioo a b)), F x = 0 := by
    refine (MeasureTheory.lintegral_eq_zero_iff' hF.aemeasurable).mp ?_
    simpa using hint
  have hzero : (volume : Measure ℝ) ({y : ℝ | F y ≠ 0} ∩ Set.Ioo a b) = 0 := by
    have h1 := MeasureTheory.ae_iff.mp hF0
    have hmeas : MeasurableSet {y : ℝ | F y ≠ 0} := (hF (measurableSet_singleton 0)).compl
    rw [Measure.restrict_apply hmeas] at h1
    exact h1
  have hsub : Set.Ioo a b ⊆ {y : ℝ | F y ≠ 0} ∩ Set.Ioo a b := by
    intro y hy
    refine ⟨?_, hy⟩
    have hh := h y hy
    simp only [zero_add] at hh
    intro hzy
    rw [hzy, mul_zero] at hh
    exact lt_irrefl _ hh
  exact hvolne0 (le_antisymm (by rw [← hzero]; exact measure_mono hsub) bot_le)

end Commons.Analysis.Measure

/-- The same as `exists_le_of_lintegral_le`, with a.e.-measurability instead of measurability. -/
theorem exists_le_of_lintegral_le_ae (F : ℝ → ENNReal) (hF : AEMeasurable F (volume : Measure ℝ))
    {a b : ℝ} (hab : a < b) {K : ENNReal}
    (hint : ∫⁻ x in Set.Ioo a b, F x ∂(volume : Measure ℝ) ≤ K) (hKtop : K ≠ ⊤) :
    ∃ y ∈ Set.Ioo a b, ENNReal.ofReal (b - a) * F y ≤ (K + K) := by
  by_contra h
  push_neg at h
  have hvol : (volume : Measure ℝ) (Set.Ioo a b) = ENNReal.ofReal (b - a) := Real.volume_Ioo
  have hvolne0 : (volume : Measure ℝ) (Set.Ioo a b) ≠ 0 := by
    rw [hvol]; exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hvollt : (volume : Measure ℝ) (Set.Ioo a b) ≠ ⊤ := by
    rw [hvol]; exact ENNReal.ofReal_ne_top
  have hlow : (volume : Measure ℝ) (Set.Ioo a b) * ((K + K) / (volume (Set.Ioo a b)))
      ≤ ∫⁻ x in Set.Ioo a b, F x ∂(volume : Measure ℝ) := by
    calc (volume : Measure ℝ) (Set.Ioo a b) * ((K + K) / (volume (Set.Ioo a b)))
        = ∫⁻ x in Set.Ioo a b, (K + K) / (volume (Set.Ioo a b)) ∂(volume : Measure ℝ) :=
          (by rw [MeasureTheory.setLIntegral_const (μ := volume) (Set.Ioo a b)
              ((K + K) / (volume (Set.Ioo a b))), mul_comm])
      _ ≤ ∫⁻ x in Set.Ioo a b, F x ∂(volume : Measure ℝ) := by
          refine setLIntegral_mono' measurableSet_Ioo fun y hy => ?_
          rw [ENNReal.div_le_iff_le_mul (Or.inl hvolne0) (Or.inl hvollt)]
          rw [mul_comm]
          exact le_of_lt (by simpa only [hvol, mul_comm] using h y hy)
  have hK2 : K + K ≤ K := by
    refine le_trans ?_ hint
    calc K + K = (volume : Measure ℝ) (Set.Ioo a b) * ((K + K) / (volume (Set.Ioo a b))) :=
          (ENNReal.mul_div_cancel hvolne0 hvollt).symm
      _ ≤ _ := hlow
  have hK0 : K = 0 := by
    by_contra h0
    exact absurd hK2 (not_le.mpr (ENNReal.lt_add_right hKtop h0))
  subst hK0
  have hF0 : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Set.Ioo a b)), F x = 0 := by
    refine (MeasureTheory.lintegral_eq_zero_iff' (hF.mono_measure Measure.restrict_le_self)).mp ?_
    simpa using hint
  have hzero : ((volume : Measure ℝ).restrict (Set.Ioo a b)) {y : ℝ | F y ≠ 0} = 0 :=
    MeasureTheory.ae_iff.mp hF0
  have hsub : Set.Ioo a b ⊆ {y : ℝ | F y ≠ 0} := by
    intro y hy
    have hh := h y hy
    simp only [zero_add] at hh
    intro hzy
    rw [hzy, mul_zero] at hh
    exact lt_irrefl _ hh
  have hzero' : (volume : Measure ℝ) (Set.Ioo a b) ≤ 0 := by
    calc (volume : Measure ℝ) (Set.Ioo a b)
        = ((volume : Measure ℝ).restrict (Set.Ioo a b)) (Set.Ioo a b) :=
          (Measure.restrict_apply_self _ _).symm
      _ ≤ ((volume : Measure ℝ).restrict (Set.Ioo a b)) {y : ℝ | F y ≠ 0} :=
          measure_mono hsub
      _ = 0 := hzero
  exact hvolne0 (le_antisymm hzero' bot_le)


open _root_.MeasureTheory Finset
open scoped BigOperators _root_.ENNReal _root_.Topology

namespace Commons.Analysis.Fourier

noncomputable section

variable {K : ℕ}

/-!
# The Tonelli / `z`-integration step of Bourgain's smooth-window estimate

Starting from `chain_bound_at_z` (the per-`z` chained entropy bound) we integrate in `z`.  The
plan (see `STATUS_entropy_step.md`):

1. `bandMaxTr Ψ lam H S y` is the maximal function of the translate `T_y H` with the inner sup
   truncated at level `S`; by `bandMax_translate` (framework) and the phase identity
   `e^{Iλy}·e^{-Iλz} = e^{Iλ(y-z)}` it equals the `chain_bound_at_z` integrand with `y - z`.
2. Tonelli in `(y,z)` plus the range inclusion `(0, 9/10) - z ⊆ (-z, 1-z)` gives
   `∫_{y∈(0,9/10)} bandMaxTr y dy ≤ ∫_z (chain bound at z)`.
3. The `z`-integral of the chain bound is finite: `∫_z (curveRad)² ≤ ∫_z (winFL2)²` (the
   sup-norm/dilation bound extracted from `bourgain_entropy_integral_l2_l2vec`) and
   `∫_z I(z)²` is the deep input `bourgain_entropy_integral_l2_l2vec` itself
   (`I(z) = ∫_r min (√K) (winML2 Ψ H z r)^{1/2}`), with `bandSq` on the right.
4. `exists_le_of_lintegral_le` (proved in `Submission/Work/Analysis/Measure/`) then selects a
   single `y ∈ (0, 9/10)` with `ofReal (9/10) * bandMaxTr y ≤ 2 K₀`.
-/

/-- The (truncated) maximal function of the translate `T_y H`, as a function of the shift `y`. -/
noncomputable def bandMaxTr (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (S : ℕ) (y : ℝ) : ENNReal :=
  ∫⁻ z, (⨆ i : Fin (S+2), ‖∑ k : Fin K, curvePt Ψ H (i:ℕ) z k
    * Complex.exp (Complex.I * (lam k : ℂ) * ((y - z : ℝ) : ℂ))‖ₑ) ^ (2:ℝ)

/-- The same quantity written with the phase split off, i.e. the form produced by
`bandMax_translate`. -/
lemma bandMaxTr_eq (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (S : ℕ) (y : ℝ) :
    bandMaxTr Ψ lam H S y
      = ∫⁻ z, (⨆ i : Fin (S+2), ‖∑ k : Fin K,
          Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) * curvePtPh Ψ lam H (i:ℕ) z k‖ₑ) ^ (2:ℝ) := by
  unfold bandMaxTr
  refine lintegral_congr fun z => ?_
  have h : (fun i : Fin (S+2) => ‖∑ k : Fin K, curvePt Ψ H (i:ℕ) z k
        * Complex.exp (Complex.I * (lam k : ℂ) * ((y - z : ℝ) : ℂ))‖ₑ)
      = fun i : Fin (S+2) => ‖∑ k : Fin K,
          Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) * curvePtPh Ψ lam H (i:ℕ) z k‖ₑ := by
    funext i
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold curvePtPh
    rw [show Complex.exp (Complex.I * (lam k : ℂ) * ((y - z : ℝ) : ℂ))
        = Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))
          * Complex.exp (-(Complex.I * (lam k : ℂ) * (z : ℂ))) from by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  rw [h]

end

end Commons.Analysis.Fourier


open _root_.MeasureTheory Finset
open scoped BigOperators _root_.ENNReal _root_.Topology

namespace Commons.Analysis.Fourier

noncomputable section

variable {K : ℕ}

/-!
# The two analytic inputs of the `z`-integration step

The composition of `chain_bound_at_z` with `lintegral_shift_le` reduces the Tonelli step to two
estimates, one for each summand of the chain bound's right-hand side.  They are stated here in the
exact form the composition consumes.

* **(A) the sup-norm (dilation) input**: `∫_z (winFL2 Ψ H z)² ≤ C · bandSq H`.
  `winFL2 Ψ H z` is the sup over `t > 0` of the `ℓ²`-norm of the windowed curve, and
  `curveRad Ψ H (S+1) z ≤ winFL2 Ψ H z` (a max over the dyadic points is a sup over `t > 0`).
  Recipe: copy `hh`/`hFle`/`hhfin` out of the proof of `bourgain_entropy_integral_l2_l2vec`
  (lines ~415–470 of `bourgain_entropy_l2_vec.lean`): `winFL2 ≤ hh` pointwise, and
  `∫ hh² ≤ ofReal (C₀² C₁²) · A` where `A = ∫⁻ x, ofReal (∑ k, ‖H k x‖²)` is *definitionally*
  `bandSq H`.

* **(B) the deep entropy input**: `∫_z I(z)² ≤ ofReal ((C log²(K+2))²) · bandSq H` where
  `I(z) = ∫⁻ r in Ioi 0, min (ofReal √K) ((winML2 Ψ H z r) ^ (1/2))`.
  This is literally `bourgain_entropy_integral_l2_l2vec Ψ M hM` (with `winML2` respelled via
  `Metric.coveringNumber`), under the extra hypothesis `H k ∈ L^∞` (needed for the
  boundedness of the curve range).  The `L^∞` hypothesis is discharged later by truncation +
  Fatou.
-/

/-- `curveRad` is dominated by `winFL2` (a max over dyadic points is a sup over all `t > 0`). -/
theorem curveRad_le_winFL2 (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) :
    ENNReal.ofReal (curveRad Ψ H S z) ≤ winFL2 Ψ H z := by
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (S+1)))
    (fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖) Finset.univ_nonempty
  have hsup : Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖)
      = ‖curveVec Ψ H S z i₀‖ :=
    le_antisymm (Finset.sup'_le Finset.univ_nonempty (fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖)
        (fun i _ => hi₀ i (Finset.mem_univ i)))
      (Finset.le_sup' (fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖) (Finset.mem_univ i₀))
  calc ENNReal.ofReal (curveRad Ψ H S z)
      = ENNReal.ofReal ‖curveVec Ψ H S z i₀‖ := by
        unfold curveRad
        rw [hsup]
    _ = ‖winCurveL2 Ψ H z ⟨scaleTj (i₀:ℕ), scaleTj_pos (i₀:ℕ)⟩‖ₑ := by
        unfold curveVec
        rw [ofReal_norm]
    _ ≤ winFL2 Ψ H z := by
        unfold winFL2
        exact le_iSup (fun t : {t : ℝ // 0 < t} => ‖winCurveL2 Ψ H z t‖ₑ) _

end

end Commons.Analysis.Fourier

open scoped _root_.ENNReal
open _root_.MeasureTheory

namespace Commons.Analysis.Measure

private lemma setLIntegral_comp_sub (F : ℝ → ENNReal) (z a b : ℝ) :
    ∫⁻ y in Set.Ioo a b, F (y - z) = ∫⁻ w in Set.Ioo (a - z) (b - z), F w := by
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo]
  have h : ∀ y : ℝ, (Set.Ioo a b).indicator (fun y => F (y - z)) y
      = (Set.Ioo (a - z) (b - z)).indicator F (y - z) := by
    intro y
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hy : y ∈ Set.Ioo a b
    · rw [if_pos hy, if_pos ⟨by linarith [hy.1], by linarith [hy.2]⟩]
    · rw [if_neg hy]
      by_cases hy' : y - z ∈ Set.Ioo (a - z) (b - z)
      · exact absurd ⟨by linarith [hy'.1], by linarith [hy'.2]⟩ hy
      · rw [if_neg hy']
  rw [lintegral_congr h]
  exact lintegral_add_right_eq_self (fun w : ℝ => (Set.Ioo (a - z) (b - z)).indicator F w) (-z)

/-- Tonelli for the shifted integrand. -/
theorem lintegral_shift_le (f : ℝ → ℝ → ENNReal) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hf : AEMeasurable (Function.uncurry fun y z : ℝ => f z (y - z))
      ((volume.restrict (Set.Ioo (0:ℝ) δ)).prod (volume : Measure ℝ))) :
    ∫⁻ y in Set.Ioo (0:ℝ) δ, ∫⁻ z, f z (y - z)
      ≤ ∫⁻ z, ∫⁻ w in Set.Ioc (-z) (-z + 1), f z w := by
  rw [MeasureTheory.lintegral_lintegral_swap hf]
  refine lintegral_mono fun z => ?_
  rw [setLIntegral_comp_sub]
  exact lintegral_mono_set (fun w hw => ⟨by linarith [hw.1], by linarith [hw.2, hδ1]⟩)

end Commons.Analysis.Measure


open _root_.MeasureTheory Finset
open scoped BigOperators _root_.ENNReal _root_.Topology

namespace Commons.Analysis.Fourier

noncomputable section

variable {K : ℕ}

/-- The per-`z` integrand consumed by `chain_bound_at_z` and `lintegral_shift_le`. -/
noncomputable def tonelliFun (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (S : ℕ) (z w : ℝ) : ENNReal :=
  ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K, curvePt Ψ H (i:ℕ) z k
    * Complex.exp (Complex.I * (lam k : ℂ) * (w : ℂ))‖) ^ (2:ℝ)

/-- `ofReal` of the finite sup `curveRad` is the supremum of the `enorm`s of the curve points. -/
lemma ofReal_curveRad_eq_iSup (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) :
    ENNReal.ofReal (curveRad Ψ H S z)
      = ⨆ i : Fin (S+1), ‖curveVec Ψ H S z i‖ₑ := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i₀, _, hi₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (S+1)))
      (fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖) Finset.univ_nonempty
    have hsup : Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖) = ‖curveVec Ψ H S z i₀‖ :=
      le_antisymm (Finset.sup'_le Finset.univ_nonempty _
          (fun i _ => hi₀ i (Finset.mem_univ i)))
        (Finset.le_sup' (fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖) (Finset.mem_univ i₀))
    have hstep : ENNReal.ofReal (curveRad Ψ H S z) = ‖curveVec Ψ H S z i₀‖ₑ := by
      rw [curveRad, hsup, ofReal_norm]
    rw [hstep]
    exact le_iSup (fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖ₑ) i₀
  · refine iSup_le fun i => ?_
    have hle : ‖curveVec Ψ H S z i‖ ≤ curveRad Ψ H S z := by
      rw [curveRad]
      exact Finset.le_sup' (fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖) (Finset.mem_univ i)
    calc ‖curveVec Ψ H S z i‖ₑ = ENNReal.ofReal ‖curveVec Ψ H S z i‖ := by rw [ofReal_norm]
      _ ≤ ENNReal.ofReal (curveRad Ψ H S z) := ENNReal.ofReal_le_ofReal hle

/-- **Item 2, algebraic part**: pull the constant and use linearity, given the two integral
bounds (inputs (A) and (B)) and the measurability of the `curveRad` summand. -/
theorem z_integral_le (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) {C CA CB : ℝ}
    (hC : 0 < C)
    (hmA : AEMeasurable (fun z : ℝ => (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)) volume)
    (hA : ∫⁻ z, (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
      ≤ ENNReal.ofReal CA * bandSq H)
    (hB : ∫⁻ z, (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
          ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ) ≤ ENNReal.ofReal CB * bandSq H) :
    ∫⁻ z, ENNReal.ofReal (C ^ 2) *
        (256 * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
          + 16 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                    ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ))
      ≤ ENNReal.ofReal (C ^ 2) *
          (256 * (ENNReal.ofReal CA * bandSq H) + 16 * (ENNReal.ofReal CB * bandSq H)) := by
  have h1 : (∫⁻ z, ENNReal.ofReal (C ^ 2) *
        ((256:ENNReal) * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
          + 16 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                    ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ)))
      = ENNReal.ofReal (C ^ 2) * (∫⁻ z,
        ((256:ENNReal) * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
          + 16 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                    ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ))) :=
    lintegral_const_mul' (ENNReal.ofReal (C ^ 2)) _ (ENNReal.ofReal_ne_top)
  have h2 : (∫⁻ z, ((256:ENNReal) * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
          + 16 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                    ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ)))
      = (256:ENNReal) * (∫⁻ z, (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ))
        + 16 * (∫⁻ z, (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                    ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ)) := by
    rw [lintegral_add_left' (f := fun z : ℝ =>
      (256:ENNReal) * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ))
      (aemeasurable_const.mul hmA)]
    rw [lintegral_const_mul'' 256 hmA, lintegral_const_mul' 16 _ (by norm_num)]
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hA bot_le) (mul_le_mul_of_nonneg_left hB bot_le)) bot_le

end

end Commons.Analysis.Fourier

open scoped _root_.ENNReal

namespace Commons.Analysis.Maximal

/-- **Abstract geometric iteration with a state-dependent shift.**

If `M x ≤ A·SQ x + M (T x)`, the shifted state contracts the energy,
`SQ (T x) ≤ θ²·SQ x`, there is an a priori bound `M x ≤ CK·SQ x`, and `2 θ² < 1`, then
`M x ≤ (A/(1-θ²))·SQ x`.  The shift `T` may depend on the state; this is the form in which
Bourgain's `u`-averaging bootstrap is applied (the shift is chosen by averaging over the
translation parameter). -/
theorem iter_bound_shift {X : Type*} (M SQ : X → ENNReal) (T : X → X) {A ρ CK : ℝ}
    (hA : 0 ≤ A) (hApos : 0 < A) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (hCK : 0 ≤ CK)
    (hone : ∀ x : X, M x ≤ ENNReal.ofReal A * SQ x + 2 * M (T x))
    (hcon : ∀ x : X, 2 * SQ (T x) ≤ ENNReal.ofReal ρ * SQ x)
    (hap : ∀ x : X, M x ≤ ENNReal.ofReal CK * SQ x) (x : X) :
    M x ≤ ENNReal.ofReal (A / (1 - ρ)) * SQ x := by
  set xₙ : ℕ → X := fun n => Nat.rec x (fun _ y => T y) n with hxndef
  have hxₙ_succ : ∀ n, xₙ (n+1) = T (xₙ n) := fun n => rfl
  have hrec : ∀ n, M (xₙ n) ≤ ENNReal.ofReal A * SQ (xₙ n) + 2 * M (xₙ (n+1)) := by
    intro n
    rw [hxₙ_succ n]
    exact hone (xₙ n)
  have hsq : ∀ n, 2 * SQ (xₙ (n+1)) ≤ ENNReal.ofReal ρ * SQ (xₙ n) := by
    intro n
    rw [hxₙ_succ n]
    exact hcon (xₙ n)
  have hsq_pow : ∀ n, 2 ^ n * SQ (xₙ n) ≤ (ENNReal.ofReal ρ) ^ n * SQ x := by
    intro n
    induction n with
    | zero => simp [hxndef]
    | succ n ih =>
        calc 2 ^ (n+1) * SQ (xₙ (n+1))
            = 2 ^ n * (2 * SQ (xₙ (n+1))) := by ring
          _ ≤ 2 ^ n * (ENNReal.ofReal ρ * SQ (xₙ n)) :=
              mul_le_mul_of_nonneg_left (hsq n) (bot_le)
          _ = ENNReal.ofReal ρ * (2 ^ n * SQ (xₙ n)) := by ring
          _ ≤ ENNReal.ofReal ρ * ((ENNReal.ofReal ρ) ^ n * SQ x) :=
              mul_le_mul_of_nonneg_left ih (bot_le)
          _ = (ENNReal.ofReal ρ) ^ (n+1) * SQ x := by ring
  have htot : ∀ n, M x
      ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i) * SQ x
        + 2 ^ n * M (xₙ n) := by
    intro n
    induction n with
    | zero => simp [hxndef]
    | succ n ih =>
        calc M x
            ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i) * SQ x
              + 2 ^ n * M (xₙ n) := ih
          _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i) * SQ x
              + 2 ^ n * (ENNReal.ofReal A * SQ (xₙ n) + 2 * M (xₙ (n+1))) :=
              add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hrec n) (bot_le))
          _ = (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i) * SQ x
              + ENNReal.ofReal A * (2 ^ n * SQ (xₙ n)) + 2 ^ (n+1) * M (xₙ (n+1)) := by ring
          _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i) * SQ x
              + ENNReal.ofReal A * ((ENNReal.ofReal ρ) ^ n * SQ x)
              + 2 ^ (n+1) * M (xₙ (n+1)) := by
              refine add_le_add (add_le_add (le_refl _) ?_) (le_refl _)
              exact mul_le_mul_of_nonneg_left (hsq_pow n) (bot_le)
          _ = (∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i) * SQ x
              + 2 ^ (n+1) * M (xₙ (n+1)) := by
              rw [Finset.sum_range_succ]; ring
  have htail : ∀ n, 2 ^ n * M (xₙ n) ≤ ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ n * SQ x := by
    intro n
    calc 2 ^ n * M (xₙ n) ≤ 2 ^ n * (ENNReal.ofReal CK * SQ (xₙ n)) :=
          mul_le_mul_of_nonneg_left (hap (xₙ n)) (bot_le)
      _ = ENNReal.ofReal CK * (2 ^ n * SQ (xₙ n)) := by ring
      _ ≤ ENNReal.ofReal CK * ((ENNReal.ofReal ρ) ^ n * SQ x) :=
          mul_le_mul_of_nonneg_left (hsq_pow n) (bot_le)
      _ = ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ n * SQ x := by ring
  have hcast1 : ∀ n, (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
      = ENNReal.ofReal (A * (∑ i ∈ Finset.range n, ρ ^ i)) := by
    intro n
    have hterm : ∀ i, ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i
        = ENNReal.ofReal (A * ρ^i) := by
      intro i
      rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_pow (hρ0)]
    rw [Finset.sum_congr rfl (fun i _ => hterm i),
      ← ENNReal.ofReal_sum_of_nonneg
        (fun i _ => mul_nonneg hA (pow_nonneg (hρ0) i))]
    conv_rhs => rw [Finset.mul_sum]
  have hcast2 : ∀ n, ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ n
      = ENNReal.ofReal (CK * ρ ^ n) := by
    intro n
    rw [ENNReal.ofReal_mul hCK, ENNReal.ofReal_pow (hρ0)]
  have hcast : ∀ n, ((∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ n)
      = ENNReal.ofReal (A * (∑ i ∈ Finset.range n, ρ ^ i) + CK * ρ ^ n) := by
    intro n
    rw [hcast1 n, hcast2 n, ← ENNReal.ofReal_add
      (mul_nonneg hA (Finset.sum_nonneg fun i _ => pow_nonneg (hρ0) i))
      (mul_nonneg hCK (pow_nonneg (hρ0) _))]
  have hgeo : ∀ n, (∑ i ∈ Finset.range n, ρ^i) ≤ (1 - ρ)⁻¹ := by
    intro n
    have hden : 0 < 1 - ρ := by linarith
    rw [inv_eq_one_div, le_div_iff₀ hden]
    have h1 : (∑ i ∈ Finset.range n, ρ^i) * (1 - ρ) = 1 - ρ^n := by
      have hg := geom_sum_mul ρ n
      rw [show (1:ℝ) - ρ = -(ρ - 1) by ring, mul_neg, hg]
      ring
    rw [h1]
    have : (0:ℝ) ≤ ρ^n := pow_nonneg (hρ0) n
    linarith
  have hkey : ∀ ε : NNReal, 0 < ε → ∃ n : ℕ, ((∑ i ∈ Finset.range (n+1),
      ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1))
      ≤ ENNReal.ofReal (A / (1 - ρ)) + (ε : ENNReal) := by
    intro ε hε
    have hlt : ρ < 1 := hρ
    have hε' : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
    obtain ⟨n, hn⟩ : ∃ n : ℕ, CK * ρ^(n+1) ≤ (ε : ℝ) := by
      rcases eq_or_lt_of_le hCK with h0 | hpos
      · refine ⟨0, ?_⟩
        rw [← h0, zero_mul]
        exact hε'.le
      · obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ) < (ε:ℝ)/CK) hlt
        refine ⟨m, le_of_lt ?_⟩
        calc CK * ρ^(m+1) = (CK * ρ^m) * ρ := by ring
          _ ≤ (CK * ρ^m) * 1 :=
              mul_le_mul_of_nonneg_left hlt.le (by positivity)
          _ = CK * ρ^m := by ring
          _ < CK * ((ε:ℝ)/CK) := mul_lt_mul_of_pos_left hm hpos
          _ = (ε:ℝ) := by field_simp
    refine ⟨n, ?_⟩
    calc ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
          + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1))
        = ENNReal.ofReal (A * (∑ i ∈ Finset.range (n+1), ρ ^ i) + CK * ρ ^ (n+1)) :=
          hcast (n+1)
      _ ≤ ENNReal.ofReal (A * (1 - ρ)⁻¹ + (ε : ℝ)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hge := hgeo (n+1)
          have hA1 : A * (∑ i ∈ Finset.range (n+1), ρ^i) ≤ A * (1 - ρ)⁻¹ :=
            mul_le_mul_of_nonneg_left hge hA
          linarith [hn]
      _ = ENNReal.ofReal (A * (1 - ρ)⁻¹) + ENNReal.ofReal ((ε : ℝ)) :=
          ENNReal.ofReal_add (by positivity) (by positivity)
      _ = ENNReal.ofReal (A / (1 - ρ)) + (ε : ENNReal) := by
          rw [ENNReal.ofReal_coe_nnreal]
          congr 1
  have hlimShift : (⨅ n, ((∑ i ∈ Finset.range (n+1),
      ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1))) ≤ ENNReal.ofReal (A / (1 - ρ)) := by
    refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
    obtain ⟨n, hn⟩ := hkey ε hε
    exact (iInf_le _ n).trans hn
  have hX1 : ∀ n : ℕ, ENNReal.ofReal A ≤ (∑ i ∈ Finset.range (n+1),
      ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1) := by
    intro n
    have h1 : ENNReal.ofReal A ≤ ∑ i ∈ Finset.range (n+1),
        ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i := by
      have := Finset.single_le_sum
        (f := fun i => ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
        (fun i _ => bot_le) (Finset.mem_range.mpr (Nat.succ_pos n))
      simpa using this
    exact le_add_right h1
  have hLpos : 0 < ⨅ n, ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1)) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hApos) (le_iInf fun n => hX1 n)
  have hfin : M x ≤ ⨅ n, ((∑ i ∈ Finset.range (n+1),
      ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1)) * SQ x := by
    refine le_iInf fun n => ?_
    calc M x
        ≤ (∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i) * SQ x
          + 2 ^ (n+1) * M (xₙ (n+1)) := htot (n+1)
      _ ≤ (∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i) * SQ x
          + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1) * SQ x :=
          add_le_add (le_refl _) (htail (n+1))
      _ = ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
            + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1)) * SQ x := by ring
  calc M x
      ≤ ⨅ n, ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
          + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1)) * SQ x := hfin
    _ = (⨅ n, ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
          + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1))) * SQ x :=
        (ENNReal.iInf_mul (f := fun n => (∑ i ∈ Finset.range (n+1),
            ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
            + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1))
          (a := SQ x) (fun _ h0 => absurd h0 hLpos.ne')).symm
    _ ≤ ENNReal.ofReal (A / (1 - ρ)) * SQ x :=
        mul_le_mul_of_nonneg_right hlimShift bot_le

end Commons.Analysis.Maximal


open _root_.MeasureTheory Finset
open scoped BigOperators _root_.ENNReal _root_.Topology FourierTransform

set_option maxHeartbeats 4000000

namespace Commons.Analysis.Fourier

noncomputable section

variable {K : ℕ}

/-! ### Elementary `ENNReal` suprema lemmas -/

/-- The partial suprema `S ↦ ⨆_{i < S+2} f i` are monotone. -/
lemma iSup_fin_succ_mono (f : ℕ → ENNReal) :
    Monotone (fun S : ℕ => ⨆ i : Fin (S+2), f (i:ℕ)) := by
  intro S S' h
  refine iSup_le fun i => ?_
  exact le_iSup (fun i' : Fin (S'+2) => f (i':ℕ)) (Fin.castLE (by omega) i)

/-- The partial suprema `S ↦ ⨆_{i < S+2} f i` increase to `⨆ j, f j`. -/
lemma iSup_fin_succ_eq_iSup_nat (f : ℕ → ENNReal) :
    (⨆ S : ℕ, ⨆ i : Fin (S+2), f (i:ℕ)) = ⨆ j : ℕ, f j := by
  refine le_antisymm ?_ ?_
  · exact iSup_le fun S => iSup_le fun i => le_iSup (fun j : ℕ => f j) (i:ℕ)
  · refine iSup_le fun j => ?_
    exact le_trans (le_iSup (fun i : Fin (j+2) => f (i:ℕ)) ⟨j, by omega⟩)
      (le_iSup (fun S : ℕ => ⨆ i : Fin (S+2), f (i:ℕ)) j)

/-- The `ℓ²` energy is finite for an `L²` tuple. -/
lemma bandSq_lt_top (H : Fin K → ℝ → ℂ) (hH : ∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) :
    bandSq H < ⊤ := by
  unfold bandSq
  have hcongr : (fun x : ℝ => ENNReal.ofReal (∑ k : Fin K, ‖H k x‖ ^ 2))
      = fun x => ∑ k : Fin K, ENNReal.ofReal (‖H k x‖ ^ 2) := by
    funext x
    exact ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)
  rw [hcongr, lintegral_finsetSum' (Finset.univ)
    (f := fun k : Fin K => fun x : ℝ => ENNReal.ofReal (‖H k x‖ ^ 2))
    (fun k _ => ((hH k).aemeasurable.norm.pow_const 2).ennreal_ofReal)]
  refine ENNReal.sum_lt_top.mpr fun k _ => ?_
  have h1 : Integrable (fun x : ℝ => ‖H k x‖ ^ 2) volume := by
    have := (hH k).integrable_norm_rpow (p := 2) (by norm_num) (by norm_num)
    simpa using this
  have h2 := h1.lintegral_lt_top
  simpa only [enorm_eq_ofReal_norm'] using h2

/-! ### The band-limited `K`-function maximal bound -/

/-- Membership in `L²` is preserved by the translate `transH` / the difference `shiftH`. -/
lemma memLp_transH {H : Fin K → ℝ → ℂ} (hH : ∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ))
    (y : ℝ) : ∀ k : Fin K, MemLp (transH H y k) 2 (volume : Measure ℝ) := fun k =>
  (hH k).comp_measurePreserving (measurePreserving_add_right volume y)

lemma memLp_shiftH {H : Fin K → ℝ → ℂ} (hH : ∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ))
    (y : ℝ) : ∀ k : Fin K, MemLp (shiftH H y k) 2 (volume : Measure ℝ) := fun k =>
  (hH k).sub ((hH k).comp_measurePreserving (measurePreserving_add_right volume y))

end

end Commons.Analysis.Fourier

open _root_.MeasureTheory
open scoped _root_.ENNReal FourierTransform

namespace Commons.Analysis.Fourier

/-- **The convolution theorem** (function level, `ℝ → ℂ`, `L¹` functions):
`𝓕(f ★ κ) = 𝓕f · 𝓕κ`, where `(f ★ κ)(x) = ∫ y, f y * κ (x - y)`.

(Mathlib's `Real.fourier_mul_convolution_eq`, unfolded to the integral convolution.) -/
theorem fourier_convolution (f κ : ℝ → ℂ) (hf : Integrable f (volume : Measure ℝ))
    (hκ : Integrable κ (volume : Measure ℝ)) (η : ℝ) :
    FourierTransform.fourier (fun x : ℝ => ∫ y, f y * κ (x - y)) η
      = FourierTransform.fourier f η * FourierTransform.fourier κ η := by
  have h := Real.fourier_mul_convolution_eq (f₁ := f) (f₂ := κ) hf hκ η
  have hconv : (fun x : ℝ => ∫ y, f y * κ (x - y))
      = MeasureTheory.convolution f κ (ContinuousLinearMap.mul ℂ ℂ) (volume : Measure ℝ) := by
    funext x
    rw [convolution_def]
    rfl
  rw [hconv]
  exact h

/-- **The convolution theorem with a compactly supported smooth kernel**: the slices are
`f ★ κ` with `κ = 𝓕⁻ψ`, so we record the `𝓕κ = ψ` side as well (for Schwartz kernels). -/
theorem fourier_convolution_schwartz (f : ℝ → ℂ) (κ : SchwartzMap ℝ ℂ)
    (hf : Integrable f (volume : Measure ℝ)) (η : ℝ) :
    FourierTransform.fourier (fun x : ℝ => ∫ y, f y * (κ : ℝ → ℂ) (x - y)) η
      = FourierTransform.fourier f η * FourierTransform.fourier (κ : ℝ → ℂ) η :=
  fourier_convolution f (κ : ℝ → ℂ) hf κ.integrable η

end Commons.Analysis.Fourier

open _root_.MeasureTheory
open scoped _root_.ENNReal FourierTransform

set_option maxHeartbeats 8000000

namespace Commons.Analysis.Fourier

/-- **The bracketing bridge.**  `bandSq`'s form of the energy,
`ENNReal.ofReal (∑_k ‖H_k x‖ ^ 2)`, has the (Nat) power *inside* `ofReal`; the per-slice Plancherel
identity `lintegral_slice_sq_eq` produces `(ENNReal.ofReal ‖·‖) ^ (2:ℝ)` with the exponent on the
`ENNReal`.  This lemma converts the first into the second **once**, pointwise, so that everything
downstream inherits the right normal form. -/
lemma bandSq_eq_sum_ofReal_rpow {K : ℕ} (H : Fin K → ℝ → ℂ) (x : ℝ) :
    ENNReal.ofReal (∑ k : Fin K, ‖H k x‖ ^ 2)
      = ∑ k : Fin K, (ENNReal.ofReal ‖H k x‖) ^ (2:ℝ) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun k _ => by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
      ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- **The real-valued bridge.**  For a *nonnegative* real family `a` (`‖·‖` always is),
`ofReal (∑_k a_k²) = ∑_k (ofReal a_k) ^ (2:ℝ)`.

The nonnegativity hypothesis is **not** cosmetic: `ENNReal.ofReal` truncates negatives, so without it
the identity is false (`ENNReal.ofReal_pow` itself carries `0 ≤ p`).  This is the form the slice
energy bound instantiates at `a k = ‖∫ y, f y * κ k (x - y)‖`. -/
lemma sum_sq_ofReal_eq_sum_rpow {K : ℕ} (a : Fin K → ℝ) (ha : ∀ k : Fin K, 0 ≤ a k) :
    ENNReal.ofReal (∑ k : Fin K, a k ^ 2)
      = ∑ k : Fin K, (ENNReal.ofReal (a k)) ^ (2:ℝ) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
  exact ENNReal.ofReal_pow (p := a k) (ha k) 2

/-- **The instantiation of the bridge at the slices.**  The energy integrand of the slice
construction, `ENNReal.ofReal (∑_k ‖(f ★ κ_k) x‖²)`, is rewritten *as a function* into the normal
form produced by `lintegral_slice_sq_eq`.  Doing it as a function-level `funext` (rather than inside
the integral) keeps the normal form fixed for everything downstream. -/
lemma slice_energy_integrand_eq {K : ℕ} (f : ℝ → ℂ) (κ : Fin K → ℝ → ℂ) :
    (fun x : ℝ => ENNReal.ofReal (∑ k : Fin K, ‖∫ y : ℝ, f y * κ k (x - y)‖ ^ 2))
      = fun x : ℝ => ∑ k : Fin K,
          (ENNReal.ofReal ‖∫ y : ℝ, f y * κ k (x - y)‖) ^ (2:ℝ) := by
  funext x
  exact sum_sq_ofReal_eq_sum_rpow
    (fun k : Fin K => ‖∫ y : ℝ, f y * κ k (x - y)‖) (fun _ => norm_nonneg _)

/-- **The `eLpNorm`/`enorm` bridge for an `Lp` element**: the `eLpNorm` of the representative is the
`enorm` of the `Lp` norm.  (The naive statement `eLpNorm (⇑u) 2 = ‖u‖` is a **type** error —
`eLpNorm` is `ℝ≥0∞`-valued and `‖u‖` is `ℝ`.) -/
lemma eLpNorm_coeFn_eq_enorm_norm (u : Lp ℂ 2 (volume : Measure ℝ)) :
    eLpNorm (⇑u) 2 (volume : Measure ℝ) = ‖u‖ₑ := by
  rw [← ofReal_norm, MeasureTheory.Lp.norm_def, ENNReal.ofReal_toReal]
  exact ne_of_lt (MeasureTheory.Lp.eLpNorm_lt_top u)

/-- A.e.-measurability is preserved by the `(2:ℝ)`-power on `ℝ≥0∞`. -/
lemma aemeasurable_rpow_two {a : ℝ → ENNReal} (ha : AEMeasurable a (volume : Measure ℝ)) :
    AEMeasurable (fun ξ : ℝ => (a ξ) ^ (2:ℝ)) (volume : Measure ℝ) :=
  Measurable.comp_aemeasurable (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable ha

end Commons.Analysis.Fourier

open _root_.MeasureTheory
open scoped _root_.ENNReal

namespace Commons.Analysis.Fourier

/-- **At most two cells meet.**  If the centres `c k` are `D`-separated and each `k ∈ s` has its
centre within `a < D` of `x`, then `s` has at most two elements.  (Equivalently: three pairwise
`D`-separated centres cannot all lie in an interval of length `2a < 2D`.) -/
lemma card_le_two_of_lt {K : ℕ} (c : Fin K → ℝ) {a D : ℝ}
    (hD : ∀ k l : Fin K, k ≠ l → D ≤ |c k - c l|) (haD : a < D) (x : ℝ) (s : Finset (Fin K))
    (hs : ∀ k ∈ s, |x - c k| < a) : s.card ≤ 2 := by
  by_contra hcard
  push_neg at hcard
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q, hq, hqmax⟩ := Finset.exists_max_image s c hne
  obtain ⟨p, hp, hpmin⟩ := Finset.exists_min_image s c hne
  have hcpq : c p ≤ c q := hqmax p hp
  -- a third element
  have h21 : 1 < (s.erase p).card := by
    rw [Finset.card_erase_of_mem hp]
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h21
  have hthird : ∃ t ∈ s.erase p, t ≠ q := by
    by_cases huq : u = q
    · exact ⟨v, hv, fun hvq => huv (by rw [huq, hvq])⟩
    · exact ⟨u, hu, huq⟩
  obtain ⟨t, ht, htq⟩ := hthird
  have hts : t ∈ s := Finset.mem_of_mem_erase ht
  have htp : t ≠ p := Finset.ne_of_mem_erase ht
  have hcpt : c p ≤ c t := hpmin t hts
  have hctq : c t ≤ c q := hqmax t hts
  have h1 : D ≤ c t - c p := by
    have h := hD p t (Ne.symm htp)
    rw [abs_sub_comm, abs_of_nonneg (by linarith)] at h
    linarith
  have h2 : D ≤ c q - c t := by
    have h := hD q t (Ne.symm htq)
    rw [abs_of_nonneg (by linarith)] at h
    linarith
  have h3 : c q - c p ≤ |x - c q| + |x - c p| := by
    have h := abs_sub_le (c q) x (c p)
    rw [abs_of_nonneg (by linarith)] at h
    linarith [abs_sub_comm x (c q), abs_sub_comm x (c p)]
  have h4 : |x - c q| + |x - c p| < 2 * a := by
    have := hs q hq
    have := hs p hp
    linarith
  linarith

end Commons.Analysis.Fourier

open _root_.MeasureTheory
open scoped _root_.ENNReal FourierTransform

namespace Commons.Analysis.Fourier

/-- **The `𝓕⁻`-kernel of a smooth bump.**  If `ψ` is `C^∞` and vanishes outside the cell of
half-width `R` around `c`, then `κ := 𝓕⁻ψ` is an `L¹ ∩ L²` function with `𝓕κ = ψ` (function
level). -/
lemma exists_fourierInv_kernel (ψ : ℝ → ℝ) (hψc : ContDiff ℝ (⊤ : ℕ∞) ψ) (c R : ℝ)
    (hR : 0 < R) (hψR : ∀ x : ℝ, R ≤ |x - c| → ψ x = 0) :
    ∃ κ : ℝ → ℂ, Continuous κ ∧ Integrable κ (volume : Measure ℝ) ∧
      MemLp κ 2 (volume : Measure ℝ) ∧ MemLp κ ⊤ (volume : Measure ℝ) ∧
      (∃ C : ℝ, ∀ x : ℝ, ‖κ x‖ ≤ C) ∧
      (∀ ξ : ℝ, FourierTransform.fourier κ ξ = (ψ ξ : ℂ)) := by
  have hcont : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (ψ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hψc
  have hsupp : HasCompactSupport (fun x : ℝ => (ψ x : ℂ)) :=
    HasCompactSupport.intro (isCompact_Icc (a := c - R) (b := c + R)) (fun x hx => by
      have h : R ≤ |x - c| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
        rcases hx with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [hψR x h]; simp)
  let ψcS : SchwartzMap ℝ ℂ := hsupp.toSchwartzMap hcont
  have hcoe : (⇑ψcS : ℝ → ℂ) = fun x : ℝ => (ψ x : ℂ) := rfl
  let κS : SchwartzMap ℝ ℂ := 𝓕⁻ ψcS
  have hκS : κS = 𝓕⁻ ψcS := rfl
  refine ⟨⇑κS, κS.continuous, ?_, ?_, ?_, ?_, ?_⟩
  · exact SchwartzMap.integrable κS
  · exact SchwartzMap.memLp κS (p := 2)
  · exact SchwartzMap.memLp κS (p := ⊤)
  · exact ⟨SchwartzMap.seminorm ℂ 0 0 κS, fun x => SchwartzMap.norm_le_seminorm ℂ κS x⟩
  · intro ξ
    rw [← SchwartzMap.fourier_coe, hκS, FourierInvPair.fourier_fourierInv_eq, hcoe]

end Commons.Analysis.Fourier

open _root_.MeasureTheory
open scoped _root_.ENNReal FourierTransform

namespace Commons.Analysis.Fourier

/-- **Linearity of the function-level Fourier transform**: `𝓕(f - g) = 𝓕f - 𝓕g` for `L¹` functions
`f, g`.  (The `𝐞`-form produced by `Real.fourierIntegral_convergent_iff` is converted to the
`Complex.exp`-form produced by `Real.fourier_eq'` pointwise, once.) -/
lemma fourier_sub_of_integrable (f g : ℝ → ℂ) (hf : Integrable f (volume : Measure ℝ))
    (hg : Integrable g (volume : Measure ℝ)) (ξ : ℝ) :
    FourierTransform.fourier (f - g) ξ
      = FourierTransform.fourier f ξ - FourierTransform.fourier g ξ := by
  rw [Real.fourier_eq', Real.fourier_eq', Real.fourier_eq']
  simp only [Real.inner_apply]
  have hint : ∀ (h : ℝ → ℂ), Integrable h (volume : Measure ℝ) →
      Integrable (fun x : ℝ =>
        Complex.exp ((↑(-2 * Real.pi * (x * ξ)) * Complex.I) : ℂ) • h x) (volume : Measure ℝ) := by
    intro h hh
    have hc := (Real.fourierIntegral_convergent_iff ξ).2 hh
    refine hc.congr (Filter.Eventually.of_forall fun x => ?_)
    show (𝐞 (-(inner ℝ x ξ))) • h x
      = Complex.exp ((↑(-2 * Real.pi * (x * ξ)) * Complex.I) : ℂ) • h x
    rw [Circle.smul_def, Real.fourierChar_apply, Real.inner_apply]
    congr 1
    push_cast
    ring
  have h1 := hint f hf
  have h2 := hint g hg
  have hpt : (fun x : ℝ => Complex.exp ((↑(-2 * Real.pi * (x * ξ)) * Complex.I) : ℂ) • (f - g) x)
      = fun x : ℝ => Complex.exp ((↑(-2 * Real.pi * (x * ξ)) * Complex.I) : ℂ) • f x
          - Complex.exp ((↑(-2 * Real.pi * (x * ξ)) * Complex.I) : ℂ) • g x := by
    funext x
    simp only [Pi.sub_apply, smul_sub]
  rw [hpt, MeasureTheory.integral_sub h1 h2]

end Commons.Analysis.Fourier

open _root_.MeasureTheory
open scoped _root_.ENNReal FourierTransform

namespace Commons.Analysis.Fourier

/-- **The translate rule for the one-dimensional Fourier transform** (function level):
`𝓕(f(·+y))(ξ) = e^{2πiyξ}·𝓕f(ξ)`. -/
lemma fourier_comp_add (f : ℝ → ℂ) (y η : ℝ) :
    FourierTransform.fourier (fun z : ℝ => f (z + y)) η
      = Complex.exp ((↑(2 * Real.pi * y * η) * Complex.I) : ℂ) *
        FourierTransform.fourier f η := by
  rw [Real.fourier_eq', Real.fourier_eq']
  simp only [Real.inner_apply]
  have hshift : (fun z : ℝ => Complex.exp ((↑(-2 * Real.pi * (z * η)) * Complex.I) : ℂ) • f (z + y))
      = fun z : ℝ => (fun u : ℝ =>
          Complex.exp ((↑(-2 * Real.pi * ((u - y) * η)) * Complex.I) : ℂ) • f u) (z + y) := by
    funext z
    simp only [add_sub_cancel_right]
  have hkey : (∫ z : ℝ, (fun u : ℝ =>
        Complex.exp ((↑(-2 * Real.pi * ((u - y) * η)) * Complex.I) : ℂ) • f u) (z + y))
      = ∫ u : ℝ, Complex.exp ((↑(-2 * Real.pi * ((u - y) * η)) * Complex.I) : ℂ) • f u :=
    MeasureTheory.integral_add_right_eq_self (f := fun u : ℝ =>
      Complex.exp ((↑(-2 * Real.pi * ((u - y) * η)) * Complex.I) : ℂ) • f u) y
  rw [hshift, hkey]
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [smul_eq_mul]
  rw [show (-2 * Real.pi * ((u - y) * η) : ℝ)
      = 2 * Real.pi * y * η + (-(2 * Real.pi * (u * η))) by ring]
  rw [Complex.ofReal_add]
  rw [show ((↑(2 * Real.pi * y * η) : ℂ) + ↑(-(2 * Real.pi * (u * η)))) * Complex.I
      = ↑(2 * Real.pi * y * η) * Complex.I + ↑(-(2 * Real.pi * (u * η))) * Complex.I by ring]
  rw [Complex.exp_add]
  ring

end Commons.Analysis.Fourier

open _root_.MeasureTheory
open scoped _root_.ENNReal FourierTransform

namespace Commons.Analysis.Fourier

variable {K : ℕ}

/-- The class of "admissible" `K`-tuples for the fixed-window maximal estimate: `L¹`, `L²`,
`L^∞`, and band-limited in the function-level Fourier sense. -/
def AdmB (a : ℝ) (H : Fin K → ℝ → ℂ) : Prop :=
  (∀ k : Fin K, MemLp (H k) 1 (volume : Measure ℝ)) ∧
  (∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) ∧
  (∀ k : Fin K, MemLp (H k) ⊤ (volume : Measure ℝ)) ∧
  (∀ (k : Fin K) (ξ : ℝ), a < |ξ| → 𝓕 (H k) ξ = 0)

/-- **The class `AdmB` is preserved by the shifted difference** `H ↦ H - H(·+y)`, for *every*
shift `y` (no smallness needed: the band-limitation is preserved exactly). -/
theorem admB_shiftH {a : ℝ} {H : Fin K → ℝ → ℂ} (hH : AdmB a H) (y : ℝ) :
    AdmB a (shiftH H y) := by
  obtain ⟨h1, h2, htop, hsupp⟩ := hH
  have htr : ∀ p : ℝ≥0∞, (∀ k : Fin K, MemLp (H k) p (volume : Measure ℝ)) →
      ∀ k : Fin K, MemLp (fun x : ℝ => H k (x + y)) p (volume : Measure ℝ) := fun p hp k =>
    (hp k).comp_measurePreserving (measurePreserving_add_right volume y)
  refine ⟨fun k => (h1 k).sub (htr 1 h1 k), fun k => (h2 k).sub (htr 2 h2 k),
    fun k => (htop k).sub (htr ⊤ htop k), fun k ξ hξ => ?_⟩
  have hinte : Integrable (H k) (volume : Measure ℝ) := memLp_one_iff_integrable.mp (h1 k)
  have hinte' : Integrable (fun x : ℝ => H k (x + y)) (volume : Measure ℝ) :=
    memLp_one_iff_integrable.mp (htr 1 h1 k)
  have hshift : shiftH H y k = H k - fun x : ℝ => H k (x + y) := rfl
  rw [hshift, fourier_sub_of_integrable (H k) (fun x : ℝ => H k (x + y)) hinte hinte' ξ,
    fourier_comp_add (H k) y ξ, hsupp k ξ hξ]
  ring

end Commons.Analysis.Fourier

open _root_.MeasureTheory
open scoped _root_.ENNReal FourierTransform

namespace Commons.Analysis.Fourier

/-- Multiplication by a unimodular function preserves `MemLp`. -/
lemma memLp_mul_unimodular {p : ℝ≥0∞} {g e : ℝ → ℂ} (hg : MemLp g p (volume : Measure ℝ))
    (he : AEStronglyMeasurable e (volume : Measure ℝ)) (hE : ∀ x : ℝ, ‖e x‖ = 1) :
    MemLp (fun x : ℝ => g x * e x) p (volume : Measure ℝ) := by
  have hm : AEStronglyMeasurable (fun x : ℝ => g x * e x) (volume : Measure ℝ) :=
    hg.aestronglyMeasurable.mul he
  refine hg.congr_norm hm (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, hE x, mul_one]

/-- **The modulation rule**: `𝓕(G · e^{2πi c ·})(ξ) = 𝓕G(ξ - c)`, in the normalisation used by
the slices. -/
lemma fourier_mul_exp_rule (G : ℝ → ℂ) (c η : ℝ) :
    FourierTransform.fourier
        (fun x : ℝ => G x * Complex.exp ((↑(2 * Real.pi * c * x) * Complex.I) : ℂ)) η
      = FourierTransform.fourier G (η - c) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  simp only [Real.inner_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  have hpt : Complex.exp ((↑(-2 * Real.pi * (x * η)) * Complex.I) : ℂ) *
        (G x * Complex.exp ((↑(2 * Real.pi * c * x) * Complex.I) : ℂ))
      = Complex.exp ((↑(-2 * Real.pi * (x * (η - c))) * Complex.I) : ℂ) * G x := by
    rw [show Complex.exp ((↑(-2 * Real.pi * (x * η)) * Complex.I) : ℂ) *
          (G x * Complex.exp ((↑(2 * Real.pi * c * x) * Complex.I) : ℂ))
        = (Complex.exp ((↑(-2 * Real.pi * (x * η)) * Complex.I) : ℂ) *
            Complex.exp ((↑(2 * Real.pi * c * x) * Complex.I) : ℂ)) * G x by ring,
      ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  exact hpt

/-- **The modulation shifts the band.**  If `𝓕G` vanishes outside the band of half-width `a`
around `0`, then `𝓕(G·e^{Iλ·})` vanishes outside the band of half-width `a` around `λ/(2π)`.
This is the step that turns the (cell-centred) bands of the slice kernels into the bands around
`0` required by the fixed-window crux. -/
lemma fourier_modulation_support {G : ℝ → ℂ} {lam a : ℝ} (_hG : Integrable G (volume : Measure ℝ))
    (hsupp : ∀ ξ : ℝ, a < |ξ| → FourierTransform.fourier G ξ = 0) (ξ : ℝ)
    (hξ : a < |ξ - lam / (2 * Real.pi)|) :
    FourierTransform.fourier (fun x : ℝ => G x * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))) ξ = 0 := by
  rw [show (fun x : ℝ => G x * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ)))
      = fun x : ℝ => G x * Complex.exp ((↑(2 * Real.pi * (lam / (2 * Real.pi)) * x) * Complex.I) : ℂ)
      from by
        funext x
        congr 2
        push_cast
        field_simp]
  rw [fourier_mul_exp_rule G (lam / (2 * Real.pi)) ξ]
  exact hsupp (ξ - lam / (2 * Real.pi)) hξ

end Commons.Analysis.Fourier


namespace Commons.Analysis.Fourier

open _root_.MeasureTheory Finset Function Filter
open scoped _root_.ENNReal _root_.Topology BigOperators _root_.FourierTransform

noncomputable section

/-! ## Uniform-in-`lam` constants for the entropy chain

The commons lemmas `max_finset_exponential_sum_l2` and `chain_exp_sum_le_entropy` quantify their
constant *after* `K` and `lam`; the target theorem needs a constant that is uniform in `K` and
`lam` (only the explicit `log²(K+2)` factor may depend on `K`).  This file re-proves them with the
`∃ C` moved to the front.  In both cases the constant was already independent of the parameters —
it is built from the universal constant of `separated_exponentials_near_orthogonal` — so the
proofs are the originals with the quantifier order changed. -/

private lemma iSup_finset_nonneg_u' {α : Type*} (B : Finset α) (u : α → ℝ)
    (h : ∀ a, 0 ≤ u a) : 0 ≤ (⨆ a ∈ B, u a) := by
  rcases B.eq_empty_or_nonempty with hB | hB
  · subst hB
    simp
  · obtain ⟨a₀, ha₀⟩ := hB
    have hbdd : BddAbove (Set.range (fun a => ⨆ (_ : a ∈ B), u a)) := by
      refine ⟨∑ a ∈ B, u a, ?_⟩
      rintro _ ⟨a, rfl⟩
      change (⨆ (_ : a ∈ B), u a) ≤ ∑ a ∈ B, u a
      by_cases ha : a ∈ B
      · rw [show (⨆ (_ : a ∈ B), u a) = u a from ciSup_pos (f := fun _ => u a) ha]
        exact Finset.single_le_sum (fun i _ => h i) ha
      · rw [show (⨆ (_ : a ∈ B), u a) = sSup (∅ : Set ℝ) from
            ciSup_neg (f := fun _ => u a) ha, Real.sSup_empty]
        exact Finset.sum_nonneg (fun _ _ => h _)
    have h1 : u a₀ ≤ ⨆ a, ⨆ (_ : a ∈ B), u a := by
      calc u a₀ = ⨆ (_ : a₀ ∈ B), u a₀ := (ciSup_pos (f := fun _ => u a₀) ha₀).symm
        _ ≤ ⨆ a, ⨆ (_ : a ∈ B), u a := le_ciSup hbdd a₀
    exact le_trans (h a₀) h1

/-- For a finite family of nonnegative reals the square of the supremum is at most the sum of
the squares (a consequence of `(sup u)² ≤ ∑ u²`, i.e. of the fact that a maximum of
nonnegative numbers is dominated in square by the sum of all squares). -/
private lemma iSup_finset_sq_le_sum_u' {α : Type*} (B : Finset α) (u : α → ℝ)
    (h : ∀ a, 0 ≤ u a) : (⨆ a ∈ B, u a) ^ 2 ≤ ∑ a ∈ B, (u a) ^ 2 := by
  have hnn : 0 ≤ (⨆ a ∈ B, u a) := iSup_finset_nonneg_u' B u h
  have h1 : (⨆ a ∈ B, u a) ≤ Real.sqrt (∑ a ∈ B, (u a) ^ 2) := by
    rcases isEmpty_or_nonempty α with hα | hα
    · have hB : B = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp (fun hne => hne.elim fun a _ => isEmptyElim a)
      rw [show (⨆ a : α, ⨆ (_ : a ∈ B), u a) = (⨆ a : α, (0 : ℝ)) from by
            apply iSup_congr; intro a
            rw [show (⨆ (_ : a ∈ B), u a) = sSup (∅ : Set ℝ) from
              ciSup_neg (f := fun _ => u a) (by rw [hB]; simp)]
            exact Real.sSup_empty]
      rw [Real.iSup_of_isEmpty]
      simp [hB]
    · apply ciSup_le
      intro b
      by_cases hb : b ∈ B
      · rw [show (⨆ (_ : b ∈ B), u b) = u b from ciSup_pos (f := fun _ => u b) hb]
        rw [← Real.sqrt_sq (h b)]
        exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun _ _ => sq_nonneg _) hb)
      · rw [show (⨆ (_ : b ∈ B), u b) = sSup (∅ : Set ℝ) from
            ciSup_neg (f := fun _ => u b) hb, Real.sSup_empty]
        exact Real.sqrt_nonneg _
  calc (⨆ a ∈ B, u a) ^ 2 ≤ (Real.sqrt (∑ a ∈ B, (u a) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ hnn h1 2
    _ = ∑ a ∈ B, (u a) ^ 2 := Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

private lemma norm_cexp_lin_u (lam y : ℝ) :
    ‖Complex.exp (Complex.I * (lam : ℂ) * (y : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (Complex.I * (lam : ℂ) * (y : ℂ)).re = 0 := by
    rw [Complex.mul_re, Complex.mul_re]; simp
  rw [h, Real.exp_zero]

/-- Cauchy–Schwarz: `∑ ‖d k‖ ≤ √K · √(∑ ‖d k‖²)`. -/
private lemma sum_norm_le_sqrt_card_mul_sqrt_sum_sq_u {K : ℕ} (d : Fin K → ℂ) :
    ∑ k : Fin K, ‖d k‖ ≤ Real.sqrt K * Real.sqrt (∑ k : Fin K, ‖d k‖ ^ 2) := by
  have h1 : (∑ k : Fin K, ‖d k‖ * 1) ^ 2
      ≤ (∑ k : Fin K, ‖d k‖ ^ 2) * (∑ _ : Fin K, (1 : ℝ) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖d k‖) (fun _ => 1)
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h1
  have h3 : 0 ≤ ∑ k : Fin K, ‖d k‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc ∑ k : Fin K, ‖d k‖ ≤ Real.sqrt ((∑ k : Fin K, ‖d k‖ ^ 2) * (K : ℝ)) := by
        rw [← Real.sqrt_sq h3]; exact Real.sqrt_le_sqrt h1
    _ = Real.sqrt K * Real.sqrt (∑ k : Fin K, ‖d k‖ ^ 2) := by
        rw [Real.sqrt_mul (by positivity), mul_comm]

/-- A member of a finite family of nonnegative reals is at most the finite supremum. -/
private lemma le_iSup_finset_u {α : Type*} (B : Finset α) (u : α → ℝ) (h : ∀ a, 0 ≤ u a)
    {a : α} (ha : a ∈ B) : u a ≤ ⨆ b ∈ B, u b := by
  have hbdd : BddAbove (Set.range (fun b => ⨆ (_ : b ∈ B), u b)) := by
    refine ⟨∑ b ∈ B, u b, ?_⟩
    rintro _ ⟨b, rfl⟩
    change (⨆ (_ : b ∈ B), u b) ≤ ∑ b ∈ B, u b
    by_cases hb : b ∈ B
    · rw [show (⨆ (_ : b ∈ B), u b) = u b from ciSup_pos (f := fun _ => u b) hb]
      exact Finset.single_le_sum (fun i _ => h i) hb
    · rw [show (⨆ (_ : b ∈ B), u b) = sSup (∅ : Set ℝ) from ciSup_neg (f := fun _ => u b) hb,
        Real.sSup_empty]
      exact Finset.sum_nonneg (fun _ _ => h _)
  calc u a = ⨆ (_ : a ∈ B), u a := (ciSup_pos (f := fun _ => u a) ha).symm
    _ ≤ ⨆ b, ⨆ (_ : b ∈ B), u b := le_ciSup hbdd a

/-- For a nonempty finset, the bi-supremum of a nonnegative family equals its `sup'`. -/
private lemma iSup_finset_eq_sup'_u {ι : Type*} (F : Finset ι) (hF : F.Nonempty) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) : (⨆ i ∈ F, f i) = F.sup' hF f := by
  have hFne : F.Nonempty := hF
  obtain ⟨i₀, hi₀⟩ := hFne
  haveI : Nonempty ι := ⟨i₀⟩
  have hsupnn : 0 ≤ F.sup' hF f := le_trans (hf i₀) (Finset.le_sup' f hi₀)
  refine le_antisymm ?_ (Finset.sup'_le hF f (fun i hi => le_iSup_finset_u F f hf hi))
  refine ciSup_le (fun i => ?_)
  by_cases hi : i ∈ F
  · rw [ciSup_pos (f := fun _ => f i) hi]
    exact Finset.le_sup' f hi
  · rw [ciSup_neg (f := fun _ => f i) hi, Real.sSup_empty]
    exact hsupnn

private lemma lintegral_Ioc_add_right_u (F : ℝ → ℝ≥0∞) (c : ℝ) :
    ∫⁻ y in Set.Ioc (0:ℝ) 1, F (y + c) = ∫⁻ y in Set.Ioc c (c + 1), F y := by
  rw [← MeasureTheory.lintegral_indicator measurableSet_Ioc,
      ← MeasureTheory.lintegral_indicator measurableSet_Ioc]
  have h1 : ∀ y, Set.indicator (Set.Ioc (0:ℝ) 1) (fun z => F (z + c)) y
      = Set.indicator (Set.Ioc c (c + 1)) F (y + c) := by
    intro y
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : y ∈ Set.Ioc (0:ℝ) 1
    · rw [if_pos h, if_pos ⟨by linarith [h.1], by linarith [h.2]⟩]
    · rw [if_neg h]
      by_cases h2 : y + c ∈ Set.Ioc c (c + 1)
      · exact absurd ⟨by linarith [h2.1], by linarith [h2.2]⟩ h
      · rw [if_neg h2]
  calc ∫⁻ y, Set.indicator (Set.Ioc (0:ℝ) 1) (fun z => F (z + c)) y
      = ∫⁻ y, Set.indicator (Set.Ioc c (c + 1)) F (y + c) := by simp only [h1]
    _ = ∫⁻ y, Set.indicator (Set.Ioc c (c + 1)) F y :=
        MeasureTheory.lintegral_add_right_eq_self _ c


/-! ### Covers from covering numbers -/



end

private lemma one_le_add_one_u (a : ENNReal) : 1 ≤ a + 1 := by
  calc (1:ENNReal) = 0 + 1 := by simp
    _ ≤ a + 1 := add_le_add bot_le le_rfl

/-- The last dyadic term of the entropy sum is at most one. -/
private lemma dyadic_tail_le_one_u (K S : ℕ) :
    (1/2:ℝ)^(S+1) * Real.sqrt (min (K:ℝ) ((S:ℝ) + 3)) ≤ 1 := by
  have h4 : ∀ S : ℕ, S + 3 ≤ 4^(S+1) := by
    intro S
    induction S with
    | zero => norm_num
    | succ k ih =>
        have hstep : k + 1 + 3 ≤ 4 * (k + 3) := by omega
        calc k + 1 + 3 ≤ 4 * (k + 3) := hstep
          _ ≤ 4 * 4^(k+1) := Nat.mul_le_mul_left 4 ih
          _ = 4^(k+2) := by ring
  have hsqrt : Real.sqrt (min (K:ℝ) ((S:ℝ) + 3)) ≤ 2^(S+1) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h5 : min (K:ℝ) ((S:ℝ) + 3) ≤ (S:ℝ) + 3 := min_le_right _ _
    have h6 : ((S:ℝ) + 3) ≤ (4:ℝ)^(S+1) := by exact_mod_cast h4 S
    have h7 : ((4:ℝ)^(S+1)) = (2:ℝ)^(S+1) * 2^(S+1) := by
      have : (4:ℝ) = 2 * 2 := by norm_num
      rw [this, mul_pow]
    rw [sq]
    linarith [h5, h6, h7]
  calc (1/2:ℝ)^(S+1) * Real.sqrt (min (K:ℝ) ((S:ℝ) + 3))
      ≤ (1/2:ℝ)^(S+1) * 2^(S+1) := mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = 1 := by rw [← mul_pow]; norm_num


end Commons.Analysis.Fourier


open _root_.MeasureTheory Finset Filter
open scoped _root_.Topology
open scoped BigOperators _root_.ENNReal FourierTransform

set_option maxHeartbeats 1600000

namespace Commons.Analysis.Fourier
namespace FixWin

/-! ## Part 1: the window `Ψ = 𝓕(bump)(·/2π)`

The fixed bump `SepWin.bump` (`= 1` on `[-1/2,1/2]`, `= 0` off `[-1,1]`) defines, through its
Fourier transform, the Schwartz window `winSmooth` with
`winSmooth t = ∫_{-1}^{1} bump u · e^{-I t u} du`.
This is the window whose dyadic dilations are the band-pass kernels of the target operator. -/

/-- Scaling by a nonzero constant as a continuous linear equivalence of `ℝ`. -/
noncomputable def scaleCLE (c : ℝ) (hc : c ≠ 0) : ℝ ≃L[ℝ] ℝ where
  toLinearEquiv :=
    { toFun := fun x => c * x
      invFun := fun x => c⁻¹ * x
      map_add' := fun x y => by ring
      map_smul' := fun r x => by simp only [smul_eq_mul, RingHom.id_apply]; ring
      left_inv := fun x => by field_simp
      right_inv := fun x => by field_simp }
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

@[simp] lemma scaleCLE_apply (c : ℝ) (hc : c ≠ 0) (x : ℝ) : scaleCLE c hc x = c * x := rfl

lemma scaleCLE_one_div_two_pi (t : ℝ) :
    scaleCLE (1 / (2 * Real.pi)) (by positivity : (1 / (2 * Real.pi)) ≠ 0) t
      = t / (2 * Real.pi) := by
  rw [scaleCLE_apply, one_div, inv_mul_eq_div]

/-! ## Part 2: the band kernels

The pointwise kernel of the target operator, `innerSmooth bump K lam j z`, is the sum over `k` of
the shifted band kernel `e^{-I λ_k z} · winK Ψ j z`. -/

/-- **The change of variables for a single band kernel.**  For a window with
`Ψ t = ∫_{-1}^{1} φ u e^{-Itu} du`,
`∫_{λ-h}^{λ+h} φ((θ-λ)/h) e^{-Izθ} dθ = e^{-Iλz} · h · Ψ(hz)`. -/
theorem intervalIntegral_smooth_eq_winK (φ : ℝ → ℝ) (Ψ : ℝ → ℂ) (h : ℝ) (hh : 0 < h)
    (la z : ℝ)
    (hΨ : ∀ t : ℝ, Ψ t = ∫ u in (-1)..1, (φ u : ℂ) * Complex.exp (-(Complex.I * (t : ℂ) * (u : ℂ)))) :
    (∫ θ in (la - h)..(la + h), (φ ((θ - la) / h) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))))
      = Complex.exp (-(Complex.I * (la : ℂ) * (z : ℂ))) * ((h : ℂ) * Ψ (h * z)) := by
  have h1 : (∫ θ in (la - h)..(la + h),
        (φ ((θ - la) / h) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))))
      = h • ∫ u in (-1:ℝ)..1,
        (φ (((la + h * u) - la) / h) : ℂ)
          * Complex.exp (-(Complex.I * (z : ℂ) * ((la + h * u : ℝ) : ℂ))) := by
    have hbase := intervalIntegral.smul_integral_comp_add_mul
      (a := (-1:ℝ)) (b := 1)
      (f := fun θ : ℝ => (φ ((θ - la) / h) : ℂ)
        * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ)))) h la
    rw [show la + h * (-1) = la - h by ring, show la + h * 1 = la + h by ring] at hbase
    rw [← hbase]
  have h2 : (∫ u in (-1:ℝ)..1,
        (φ (((la + h * u) - la) / h) : ℂ)
          * Complex.exp (-(Complex.I * (z : ℂ) * ((la + h * u : ℝ) : ℂ))))
      = Complex.exp (-(Complex.I * (la : ℂ) * (z : ℂ))) * Ψ (h * z) := by
    rw [hΨ (h * z), ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [show la + h * u - la = h * u by ring,
      show (h * u) / h = u by field_simp]
    have hexp : -(Complex.I * (z : ℂ) * ((la + h * u : ℝ) : ℂ))
        = -(Complex.I * (la : ℂ) * (z : ℂ)) + -(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ)) := by
      push_cast
      ring
    rw [hexp, Complex.exp_add]
    ring
  rw [h1, h2]
  rw [Complex.real_smul]
  ring

/-- The band kernel at frequency `la` and dyadic scale `j`: `e^{-I la z} · winK Ψ j z`. -/
noncomputable def bandKer (Ψ : SchwartzMap ℝ ℂ) (la : ℝ) (j : ℕ) : ℝ → ℂ :=
  fun z => Complex.exp (-(Complex.I * (la : ℂ) * (z : ℂ))) * winK Ψ j z

lemma bandKer_apply (Ψ : SchwartzMap ℝ ℂ) (la : ℝ) (j : ℕ) (z : ℝ) :
    bandKer Ψ la j z = Complex.exp (-(Complex.I * (la : ℂ) * (z : ℂ))) * winK Ψ j z := rfl

/-! ## Part 3: the oscillatory kernel `MjKer` and the band-kernel identity

`MjKer la j θ = bump((θ-la)/h_j)`, a compactly supported bounded oscillation.  The band kernel is
its oscillatory integral, `bandKer la j z = ∫ θ, MjKer la j θ · e^{-I z θ}`, and this is what makes
the convolution with the slice kernel `κ_k` (whose Fourier transform is `1` on the relevant band)
a no-op. -/

/-- A bounded measurable function supported in a compact interval is in every `L^p`. -/
lemma memLp_of_bound_support {f : ℝ → ℂ} (hmeas : AEStronglyMeasurable f (volume : Measure ℝ))
    {a b : ℝ} (hbound : ∀ θ : ℝ, ‖f θ‖ ≤ 1)
    (hsupp : ∀ θ : ℝ, θ ∉ Set.Icc a b → f θ = 0)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ⊤) :
    MemLp f p (volume : Measure ℝ) := by
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hptop hmeas]
  have hstep : ∫⁻ θ, ‖f θ‖ₑ ^ p.toReal
      ≤ ∫⁻ θ, (Set.Icc a b).indicator (fun _ => (1 : ℝ≥0∞)) θ := by
    refine lintegral_mono fun θ => ?_
    by_cases hθ : θ ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hθ]
      calc ‖f θ‖ₑ ^ p.toReal ≤ (1 : ℝ≥0∞) ^ p.toReal := by
            refine ENNReal.rpow_le_rpow ?_ (by positivity)
            rw [← ofReal_norm, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one]
            exact hbound θ
        _ = 1 := ENNReal.one_rpow _
    · rw [Set.indicator_of_notMem hθ, hsupp θ hθ, enorm_zero,
        ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp0 hptop)]
  refine lt_of_le_of_lt hstep ?_
  rw [lintegral_indicator_const measurableSet_Icc, one_mul]
  exact isCompact_Icc.measure_lt_top (μ := (volume : Measure ℝ))

/-! ## Part 4: `L^p` bookkeeping for `MjKer` and Young's inequality -/

lemma enorm_rpow_two_eq_ofReal_sq (z : ℂ) :
    ‖z‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [← ofReal_norm, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
    ← ENNReal.ofReal_pow (norm_nonneg z)]

/-! ## Part 5: the per-frequency identity -/

/-- The Fourier bound for `κ` from `𝓕κ = ψ` with `0 ≤ ψ ≤ 1`. -/
lemma norm_fourier_le_one_of_eq {κ : ℝ → ℂ} {ψ : ℝ → ℝ}
    (hκF : ∀ ξ : ℝ, FourierTransform.fourier κ ξ = (ψ ξ : ℂ))
    (hψnn : ∀ ξ : ℝ, 0 ≤ ψ ξ) (hψle : ∀ ξ : ℝ, ψ ξ ≤ 1) (ξ : ℝ) :
    ‖FourierTransform.fourier κ ξ‖ ≤ 1 := by
  rw [hκF ξ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψnn ξ)]
  exact hψle ξ

/-! ## Part 6: the fixed-window estimate for `f ∈ L¹ ∩ L²` -/

lemma integrable_mul_of_bound {f g : ℝ → ℂ} (hf : Integrable f (volume : Measure ℝ))
    {M : ℝ} (hM : 0 ≤ M) (hg : AEStronglyMeasurable g (volume : Measure ℝ))
    (hb : ∀ x : ℝ, ‖g x‖ ≤ M) : Integrable (fun x : ℝ => f x * g x) (volume : Measure ℝ) := by
  have hdom : Integrable (fun x : ℝ => M * ‖f x‖) (volume : Measure ℝ) := hf.norm.const_mul M
  refine hdom.mono' (hf.aestronglyMeasurable.mul hg) ?_
  filter_upwards with x
  rw [norm_mul]
  calc ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * M := mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
    _ = M * ‖f x‖ := by ring

/-! ## Part 7: the fixed-window estimate for `f ∈ L¹ ∩ L²` -/

/-! ## Part 8: from `L¹ ∩ L²` to `L²` -/

/-- A Schwartz function evaluated at a linear scaling is again in `L²`. -/
lemma memLp_comp_mul_left_schwartz (Ψ : SchwartzMap ℝ ℂ) (c : ℝ) (hc : c ≠ 0) :
    MemLp (fun z : ℝ => (Ψ : ℝ → ℂ) (c * z)) 2 (volume : Measure ℝ) := by
  have htemp : Function.HasTemperateGrowth (fun z : ℝ => c * z) := by
    have h : Function.HasTemperateGrowth (fun z : ℝ => z * c) := by fun_prop
    simpa [mul_comm] using h
  have hanti : AntilipschitzWith (Real.toNNReal |c|⁻¹) (fun z : ℝ => c * z) := by
    refine AntilipschitzWith.of_le_mul_dist fun u v => ?_
    have htv : (↑(Real.toNNReal |c|⁻¹) : ℝ) = |c|⁻¹ := Real.coe_toNNReal _ (inv_nonneg.mpr (abs_nonneg c))
    rw [Real.dist_eq, Real.dist_eq, htv, show c * u - c * v = c * (u - v) by ring, abs_mul,
      ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hc), one_mul]
  have hS : MemLp (⇑(SchwartzMap.compCLMOfAntilipschitz (𝕜 := ℝ) (F := ℂ) htemp hanti Ψ)) 2
      (volume : Measure ℝ) :=
    (SchwartzMap.compCLMOfAntilipschitz (𝕜 := ℝ) (F := ℂ) htemp hanti Ψ).memLp 2 (volume : Measure ℝ)
  refine hS.ae_eq (Filter.Eventually.of_forall fun z => ?_)
  rw [SchwartzMap.compCLMOfAntilipschitz_apply]
  rfl

/-- `liminf` of a sequence bounded above by `a` is at most `a`. -/
lemma liminf_le_of_le_const {u : ℕ → ℝ≥0∞} {a : ℝ≥0∞} (h : ∀ n : ℕ, u n ≤ a) :
    Filter.liminf u Filter.atTop ≤ a := by
  refine Filter.liminf_le_of_le ⟨0, Filter.Eventually.of_forall fun n => by simp⟩ ?_
  intro b hb
  obtain ⟨n, hn⟩ := Filter.Eventually.exists hb
  exact le_trans hn (h n)

end FixWin
end Commons.Analysis.Fourier


set_option maxHeartbeats 800000

namespace Commons.Analysis.Fourier

open _root_.MeasureTheory Finset Filter
open scoped BigOperators _root_.ENNReal _root_.Topology FourierTransform

noncomputable section

/-! ### The fixed bump used to split the window, and the annulus (remainder) estimate

These are the two ingredients of the reduction `φ = A + g` explained in
`Submission/Work/Analysis/Fourier/SINGLE_MULTIPLIER_REDUCTION.md`: the *fixed* bump `winA`
and the *annulus* window `g = φ - winA`, whose band-sum maximal function is bounded on `L²`
by `(8π)²` **uniformly in the annulus profile** — no dependence on the number `K` of
frequencies or on `φ`. -/


/-- The *fixed* `C^∞` bump `A` used to split a window `φ` of the target's class as `φ = A + g`:
`A = 1` on `[-1/2,1/2]`, `A = 0` off `[-1,1]`, `0 ≤ A ≤ 1`. -/
def winA (x : ℝ) : ℝ := Real.smoothTransition (2 - 2 * x) * Real.smoothTransition (2 + 2 * x)

lemma winA_contDiff (n : ℕ) : ContDiff ℝ n winA := by
  unfold winA
  exact ContDiff.mul
    ((Real.smoothTransition.contDiff (n := (n : ℕ∞))).comp (by fun_prop))
    ((Real.smoothTransition.contDiff (n := (n : ℕ∞))).comp (by fun_prop))

lemma winA_eq_one {x : ℝ} (hx : |x| ≤ 1 / 2) : winA x = 1 := by
  have h1 : (1 : ℝ) ≤ 2 - 2 * x := by
    have := (abs_le.mp hx).2; linarith
  have h2 : (1 : ℝ) ≤ 2 + 2 * x := by
    have := (abs_le.mp hx).1; linarith
  unfold winA
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, mul_one]

lemma winA_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : winA x = 0 := by
  rcases le_total 0 x with h | h
  · have h1 : 2 - 2 * x ≤ 0 := by
      have := (abs_of_nonneg h) ▸ hx; linarith
    unfold winA
    rw [Real.smoothTransition.zero_of_nonpos h1, zero_mul]
  · have h2 : 2 + 2 * x ≤ 0 := by
      have hx' : 1 ≤ -x := by rw [abs_of_nonpos h] at hx; linarith
      linarith
    unfold winA
    rw [Real.smoothTransition.zero_of_nonpos h2, mul_zero]

lemma winA_nonneg (x : ℝ) : 0 ≤ winA x := by
  unfold winA
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma winA_le_one (x : ℝ) : winA x ≤ 1 := by
  unfold winA
  exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

/-- For a window `φ` of the target's class, the annulus profile `g = φ - A` vanishes on
`[-1/2,1/2]` and off `[-1,1]`, and is bounded by `2`. -/
lemma winA_sub_supp {φ : ℝ → ℝ} (h1 : ∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1)
    (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (x : ℝ) :
    ¬ ((1 : ℝ) / 2 < |x| ∧ |x| ≤ 1) → φ x - winA x = 0 := by
  intro hx
  rcases not_and_or.mp hx with h | h
  · have : |x| ≤ 1 / 2 := le_of_not_gt h
    rw [h1 x this, winA_eq_one this, sub_self]
  · have : 1 ≤ |x| := le_of_not_ge h
    rw [h0 x this, winA_eq_zero this, sub_self]

lemma winA_sub_bound {φ : ℝ → ℝ} (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (x : ℝ) :
    ‖φ x - winA x‖ ≤ 2 := by
  have h1 := hbd x
  have h2 := winA_nonneg x
  have h3 := winA_le_one x
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h1.1, h1.2]

/-- The dyadic scale `t_j = 2^{j+1}`. -/
def scaleT (j : ℕ) : ℝ := (2 : ℝ) ^ (j + 1)

lemma scaleT_pos (j : ℕ) : 0 < scaleT j := by
  rw [scaleT]; positivity

lemma scaleT_ge_two (j : ℕ) : 2 ≤ scaleT j := by
  rw [scaleT]
  calc (2:ℝ) = 2 ^ (1:ℕ) := by norm_num
    _ ≤ 2 ^ (j + 1) := by
        apply pow_le_pow_right₀ (by norm_num) (by omega)

/-- At most two `1`-separated points of `ℝ` can lie in an interval of length `≤ 1`. -/
lemma card_le_two_separated {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    {c r : ℝ} (hr : 0 < r) (hr2 : 2 * r ≤ 1) :
    (Finset.univ.filter (fun k : Fin K => |lam k - c| ≤ r)).card ≤ 2 := by
  classical
  set S : Finset (Fin K) := Finset.univ.filter (fun k : Fin K => |lam k - c| ≤ r) with hS
  have hmem : ∀ k : Fin K, k ∈ S ↔ |lam k - c| ≤ r := by intro k; rw [hS]; simp
  have key : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → |lam x - c| = r := by
    intro x hx y hy hxy
    have h1 : 1 ≤ |lam x - lam y| := hsep x y hxy
    have h3 : |lam x - lam y| ≤ |lam x - c| + |lam y - c| := by
      calc |lam x - lam y| = |(lam x - c) - (lam y - c)| := by congr 1; ring
        _ ≤ |lam x - c| + |lam y - c| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              abs_sub_le (lam x - c) 0 (lam y - c)
    have h4 : |lam x - c| ≤ r := (hmem x).mp hx
    have h5 : |lam y - c| ≤ r := (hmem y).mp hy
    have h6 := abs_nonneg (lam x - c)
    have h7 := abs_nonneg (lam y - c)
    nlinarith [h1, h3, h4, h5, h6, h7]
  by_cases h : S.card ≤ 2
  · exact h
  · simp only [not_le] at h
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
    have hall : ∀ x ∈ S, |lam x - c| = r := by
      intro x hx
      rcases eq_or_ne x a with h' | h'
      · rw [h']; exact key a ha b hb hab
      · exact key x hx a ha h'
    have hinj : Set.InjOn lam (↑S : Set (Fin K)) := by
      intro u hu v hv huv
      by_contra hne'
      have h1 : 1 ≤ |lam u - lam v| := hsep u v hne'
      rw [huv, sub_self, abs_zero] at h1
      linarith
    have himg : (S.image lam).card = S.card := Finset.card_image_of_injOn hinj
    have hsub : S.image lam ⊆ ({c - r, c + r} : Finset ℝ) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      have := hall x hx
      rcases (abs_eq (le_of_lt hr)).mp this with h' | h'
      · simp [show lam x = c + r by linarith]
      · simp [show lam x = c - r by linarith]
    have hcard := Finset.card_le_card hsub
    have h2 : ({c - r, c + r} : Finset ℝ).card ≤ 2 := by
      rcases eq_or_ne (c - r) (c + r) with h' | h'
      · rw [h']; simp
      · rw [Finset.card_insert_of_notMem (by simp [h'])]; simp
    omega

/-- The annulus multiplier `M_j^g(η) = 2π ∑_k g(-t_j(η+λ_k))`. -/
def annulusMul {K : ℕ} (g : ℝ → ℂ) (lam : Fin K → ℝ) (j : ℕ) : ℝ → ℂ :=
  fun η => 2 * Real.pi * ∑ k : Fin K, g (-(scaleT j * (η + lam k)))

/-- Pointwise bound for the annulus multiplier. -/
lemma annulusMul_bound {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {g : ℝ → ℂ}
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (η : ℝ) (j : ℕ) :
    ‖annulusMul g lam j η‖ ≤ 8 * Real.pi := by
  rw [annulusMul]
  have hS : (Finset.univ.filter
      (fun k : Fin K => |lam k - (-η)| ≤ (scaleT j)⁻¹)).card ≤ 2 := by
    have hr : (0:ℝ) < (scaleT j)⁻¹ := inv_pos.mpr (scaleT_pos j)
    have hr2 : 2 * (scaleT j)⁻¹ ≤ 1 := by
      have h2 := scaleT_ge_two j
      have h3 : (1:ℝ) / scaleT j ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) h2
      rw [inv_eq_one_div]
      linarith
    exact card_le_two_separated hsep hr hr2
  have hzero : ∀ k : Fin K, ¬ (|lam k - (-η)| ≤ (scaleT j)⁻¹) →
      g (-(scaleT j * (η + lam k))) = 0 := by
    intro k hk
    apply hg_supp
    intro hcon
    apply hk
    have h1 : scaleT j * |η + lam k| ≤ 1 := by
      have := hcon.2
      rw [abs_neg, abs_mul, abs_of_pos (scaleT_pos j)] at this
      exact this
    rw [sub_neg_eq_add, show lam k + η = η + lam k by ring, inv_eq_one_div,
      le_div_iff₀ (scaleT_pos j), mul_comm]
    exact h1
  have hsum : ‖∑ k : Fin K, g (-(scaleT j * (η + lam k)))‖ ≤ 4 := by
    calc ‖∑ k : Fin K, g (-(scaleT j * (η + lam k)))‖
        ≤ ∑ k : Fin K, ‖g (-(scaleT j * (η + lam k)))‖ := norm_sum_le _ _
      _ = ∑ k ∈ (Finset.univ.filter (fun k : Fin K => |lam k - (-η)| ≤ (scaleT j)⁻¹)),
            ‖g (-(scaleT j * (η + lam k)))‖ := by
          refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
          intro k _ hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          rw [hzero k hk, norm_zero]
      _ ≤ ∑ k ∈ (Finset.univ.filter (fun k : Fin K => |lam k - (-η)| ≤ (scaleT j)⁻¹)),
            (2:ℝ) := by
          refine Finset.sum_le_sum (fun k _ => hg_bd _)
      _ = 2 * ((Finset.univ.filter
            (fun k : Fin K => |lam k - (-η)| ≤ (scaleT j)⁻¹)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ 2 * 2 := by
          have hcast : ((Finset.univ.filter
              (fun k : Fin K => |lam k - (-η)| ≤ (scaleT j)⁻¹)).card : ℝ) ≤ 2 := by
            exact_mod_cast hS
          linarith
      _ = 4 := by norm_num
  have hZ : (2:ℂ) * (Real.pi:ℂ) * (∑ k : Fin K, g (-(scaleT j * (η + lam k))))
      = ((2 * Real.pi : ℝ) : ℂ) * (∑ k : Fin K, g (-(scaleT j * (η + lam k)))) := by
    push_cast; ring
  calc ‖2 * Real.pi * ∑ k : Fin K, g (-(scaleT j * (η + lam k)))‖
      = 2 * Real.pi * ‖∑ k : Fin K, g (-(scaleT j * (η + lam k)))‖ := by
        rw [hZ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ ≤ 2 * Real.pi * 4 := by
        have h2 : (0:ℝ) ≤ 2 * Real.pi := by positivity
        exact mul_le_mul_of_nonneg_left hsum h2
    _ = 8 * Real.pi := by ring



lemma scaleT_mono {j j' : ℕ} (h : j ≤ j') : scaleT j ≤ scaleT j' := by
  rw [scaleT, scaleT]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

lemma scaleT_two_mul_le {j j' : ℕ} (h : j < j') : 2 * scaleT j ≤ scaleT j' := by
  have h2 : (2:ℝ) * 2 ^ (j+1) = 2 ^ (j+2) := by rw [pow_succ]; ring
  rw [scaleT, scaleT, h2]
  apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
  omega

lemma scaleT_inv_le_half (j : ℕ) : (scaleT j)⁻¹ ≤ 1/2 := by
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) (scaleT_ge_two j)

/-- At most one dyadic scale `j` contributes to the annulus multiplier at a given frequency. -/
lemma at_most_one_scale {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {g : ℝ → ℂ}
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (η : ℝ) {j j' : ℕ} (hj : ∃ k : Fin K, g (-(scaleT j * (η + lam k))) ≠ 0)
    (hj' : ∃ k : Fin K, g (-(scaleT j' * (η + lam k))) ≠ 0) : j = j' := by
  obtain ⟨k, hk⟩ := hj
  obtain ⟨k', hk'⟩ := hj'
  have hb : ∀ (m : ℕ) (l : Fin K), g (-(scaleT m * (η + lam l))) ≠ 0 →
      1/2 < scaleT m * |η + lam l| ∧ scaleT m * |η + lam l| ≤ 1 := by
    intro m l hl
    have hcon : 1/2 < |(-(scaleT m * (η + lam l)))| ∧
        |(-(scaleT m * (η + lam l)))| ≤ 1 := by
      by_contra hc
      exact hl (hg_supp _ hc)
    rw [abs_neg, abs_mul, abs_of_pos (scaleT_pos m)] at hcon
    exact hcon
  obtain ⟨hk1, hk2⟩ := hb j k hk
  obtain ⟨hk1', hk2'⟩ := hb j' k' hk'
  have htj : (0:ℝ) < scaleT j := scaleT_pos j
  have htj' : (0:ℝ) < scaleT j' := scaleT_pos j'
  -- one-sided bounds
  have hu2 : |η + lam k| ≤ (scaleT j)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ htj, mul_comm]; exact hk2
  have hu2' : |η + lam k'| ≤ (scaleT j')⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ htj', mul_comm]; exact hk2'
  have hu1 : (scaleT j)⁻¹ / 2 < |η + lam k| := by
    have h := mul_lt_mul_of_pos_left hk1 (inv_pos.mpr htj)
    have h' : (scaleT j)⁻¹ * (scaleT j * |η + lam k|) = |η + lam k| := by
      rw [← mul_assoc, inv_mul_cancel₀ htj.ne', one_mul]
    rw [h'] at h
    calc (scaleT j)⁻¹ / 2 = (scaleT j)⁻¹ * (1/2) := by ring
      _ < |η + lam k| := h
  have hu1' : (scaleT j')⁻¹ / 2 < |η + lam k'| := by
    have h := mul_lt_mul_of_pos_left hk1' (inv_pos.mpr htj')
    have h' : (scaleT j')⁻¹ * (scaleT j' * |η + lam k'|) = |η + lam k'| := by
      rw [← mul_assoc, inv_mul_cancel₀ htj'.ne', one_mul]
    rw [h'] at h
    calc (scaleT j')⁻¹ / 2 = (scaleT j')⁻¹ * (1/2) := by ring
      _ < |η + lam k'| := h
  rcases eq_or_ne k k' with hkk | hkk
  · subst hkk
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h2 : (scaleT j')⁻¹ ≤ (scaleT j)⁻¹ / 2 := by
        have hge := scaleT_two_mul_le hlt
        have h4 : (1:ℝ)/scaleT j' ≤ 1/(2*scaleT j) :=
          one_div_le_one_div_of_le (by positivity) hge
        rw [inv_eq_one_div]
        calc (1:ℝ)/scaleT j' ≤ 1/(2*scaleT j) := h4
          _ = (scaleT j)⁻¹/2 := by rw [inv_eq_one_div]; ring
      linarith [hu1, hu2']
    · have h2 : (scaleT j)⁻¹ ≤ (scaleT j')⁻¹ / 2 := by
        have hge := scaleT_two_mul_le hlt
        have h4 : (1:ℝ)/scaleT j ≤ 1/(2*scaleT j') :=
          one_div_le_one_div_of_le (by positivity) hge
        rw [inv_eq_one_div]
        calc (1:ℝ)/scaleT j ≤ 1/(2*scaleT j') := h4
          _ = (scaleT j')⁻¹/2 := by rw [inv_eq_one_div]; ring
      linarith [hu1', hu2]
  · -- different indices
    have h1 : (1:ℝ) ≤ |lam k - lam k'| := hsep k k' hkk
    have h2 : |lam k - lam k'| ≤ |η + lam k| + |η + lam k'| := by
      calc |lam k - lam k'| = |(η + lam k) - (η + lam k')| := by congr 1; ring
        _ ≤ |η + lam k| + |η + lam k'| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              abs_sub_le (η + lam k) 0 (η + lam k')
    have h3 : |η + lam k| + |η + lam k'| ≤ (scaleT j)⁻¹ + (scaleT j')⁻¹ := by linarith
    have h4 : (scaleT j)⁻¹ + (scaleT j')⁻¹ ≤ 1 := by
      linarith [scaleT_inv_le_half j, scaleT_inv_le_half j']
    have hsum1 : (scaleT j)⁻¹ + (scaleT j')⁻¹ = 1 := by linarith
    rcases lt_trichotomy j j' with hlt | heq | hgt
    · exfalso
      have hge := scaleT_two_mul_le hlt
      have h5 : (scaleT j')⁻¹ ≤ (scaleT j)⁻¹ / 2 := by
        have h6 : (1:ℝ)/scaleT j' ≤ 1/(2*scaleT j) :=
          one_div_le_one_div_of_le (by positivity) hge
        rw [inv_eq_one_div]
        calc (1:ℝ)/scaleT j' ≤ 1/(2*scaleT j) := h6
          _ = (scaleT j)⁻¹/2 := by rw [inv_eq_one_div]; ring
      have h7 : (scaleT j)⁻¹ ≤ 1/2 := scaleT_inv_le_half j
      linarith
    · exact heq
    · exfalso
      have hge := scaleT_two_mul_le hgt
      have h5 : (scaleT j)⁻¹ ≤ (scaleT j')⁻¹ / 2 := by
        have h6 : (1:ℝ)/scaleT j ≤ 1/(2*scaleT j') :=
          one_div_le_one_div_of_le (by positivity) hge
        rw [inv_eq_one_div]
        calc (1:ℝ)/scaleT j ≤ 1/(2*scaleT j') := h6
          _ = (scaleT j')⁻¹/2 := by rw [inv_eq_one_div]; ring
      have h7 : (scaleT j')⁻¹ ≤ 1/2 := scaleT_inv_le_half j'
      linarith



lemma annulusMul_ne_zero_imp {K : ℕ} {lam : Fin K → ℝ} {g : ℝ → ℂ} {j : ℕ} {η : ℝ}
    (h : annulusMul g lam j η ≠ 0) : ∃ k : Fin K, g (-(scaleT j * (η + lam k))) ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (by rw [annulusMul, Finset.sum_congr rfl (fun k _ => hc k), Finset.sum_const_zero,
    mul_zero])

lemma annulusMul_memLp {K : ℕ} {lam : Fin K → ℝ} {g : ℝ → ℂ} (hg : Measurable g)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (j : ℕ) :
    MemLp (annulusMul g lam j) ⊤ (volume : Measure ℝ) := by
  refine memLp_top_of_bound ?_ (8 * Real.pi) ?_
  · exact (Measurable.const_mul (Finset.measurable_sum _ (fun k _ =>
      hg.comp (by fun_prop : Measurable (fun η : ℝ => -(scaleT j * (η + lam k)))))) _).aestronglyMeasurable
  · filter_upwards with η
    exact annulusMul_bound hsep hg_supp hg_bd η j

lemma annulusMul_tsum_le {K : ℕ} {lam : Fin K → ℝ} {g : ℝ → ℂ} (hg : Measurable g)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (η : ℝ) :
    (∑' j : ℕ, ‖annulusMul g lam j η‖ₑ ^ (2:ℝ)) ≤ ENNReal.ofReal ((8 * Real.pi)^2) := by
  by_cases h : ∃ j : ℕ, annulusMul g lam j η ≠ 0
  · obtain ⟨j0, hj0⟩ := h
    have hzero : ∀ j : ℕ, j ≠ j0 → annulusMul g lam j η = 0 := by
      intro j hj
      by_contra hc
      exact hj (at_most_one_scale (j := j) (j' := j0) hsep hg_supp η
        (annulusMul_ne_zero_imp hc) (annulusMul_ne_zero_imp hj0))
    rw [tsum_eq_single j0 (fun j hj => by rw [hzero j hj]; simp)]
    have hb : ‖annulusMul g lam j0 η‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal ((8 * Real.pi)^2) := by
      have h1 : ‖annulusMul g lam j0 η‖ₑ ≤ ENNReal.ofReal (8 * Real.pi) := by
        rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
        exact ENNReal.ofReal_le_ofReal (annulusMul_bound hsep hg_supp hg_bd η j0)
      calc ‖annulusMul g lam j0 η‖ₑ ^ (2:ℝ)
          ≤ (ENNReal.ofReal (8 * Real.pi)) ^ (2:ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
        _ = ENNReal.ofReal ((8 * Real.pi)^2) := by
            rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity)]
    exact hb
  · push Not at h
    simp [h]


/-! ### The remainder term in the identification's frequency variable

`xiMul g lam j ξ = 2π ∑_k g(-t_j(2πξ+λ_k))` (with `t_j = 2^{j+1}`) is the annulus symbol in
the frequency variable `ξ` of `bandSum_eq_single_multiplier`.  For a profile `g` supported in the
annulus `{1/2 < |·| ≤ 1}` and bounded by `2`, at most one dyadic scale contributes at each `ξ`, so
`∑'_j ‖xiMul g lam j ξ‖² ≤ (8π)²` and the maximal multiplier is `L²`-bounded by `(8π)²`
**uniformly in `g`, `K` and the frequencies** — the elementary disjointness estimate that handles
the `φ - A` part of the window split, with no entropy input. -/

def xiMul {K : ℕ} (g : ℝ → ℂ) (lam : Fin K → ℝ) (j : ℕ) : ℝ → ℂ :=
  fun ξ => 2 * Real.pi * ∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k)))

lemma xiMul_bound {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {g : ℝ → ℂ}
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (ξ : ℝ) (j : ℕ) :
    ‖xiMul g lam j ξ‖ ≤ 8 * Real.pi := by
  rw [xiMul]
  have hS : (Finset.univ.filter
      (fun k : Fin K => |lam k - (-(2 * Real.pi * ξ))| ≤ (scaleT j)⁻¹)).card ≤ 2 := by
    have hr : (0:ℝ) < (scaleT j)⁻¹ := inv_pos.mpr (scaleT_pos j)
    have hr2 : 2 * (scaleT j)⁻¹ ≤ 1 := by
      have h2 := scaleT_ge_two j
      have h3 : (1:ℝ) / scaleT j ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) h2
      rw [inv_eq_one_div]
      linarith
    exact card_le_two_separated hsep hr hr2
  have hzero : ∀ k : Fin K, ¬ (|lam k - (-(2 * Real.pi * ξ))| ≤ (scaleT j)⁻¹) →
      g (-(scaleT j * (2 * Real.pi * ξ + lam k))) = 0 := by
    intro k hk
    apply hg_supp
    intro hcon
    apply hk
    have h1 : scaleT j * |2 * Real.pi * ξ + lam k| ≤ 1 := by
      have := hcon.2
      rw [abs_neg, abs_mul, abs_of_pos (scaleT_pos j)] at this
      exact this
    rw [show lam k - (-(2 * Real.pi * ξ)) = 2 * Real.pi * ξ + lam k by ring,
      inv_eq_one_div, le_div_iff₀ (scaleT_pos j)]
    linarith [h1]
  have hsum : ‖∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k)))‖ ≤ 4 := by
    calc ‖∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k)))‖
        ≤ ∑ k : Fin K, ‖g (-(scaleT j * (2 * Real.pi * ξ + lam k)))‖ := norm_sum_le _ _
      _ = ∑ k ∈ (Finset.univ.filter (fun k : Fin K => |lam k - (-(2 * Real.pi * ξ))| ≤ (scaleT j)⁻¹)),
            ‖g (-(scaleT j * (2 * Real.pi * ξ + lam k)))‖ := by
          refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
          intro k _ hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          rw [hzero k hk, norm_zero]
      _ ≤ ∑ k ∈ (Finset.univ.filter (fun k : Fin K => |lam k - (-(2 * Real.pi * ξ))| ≤ (scaleT j)⁻¹)),
            (2:ℝ) := by
          refine Finset.sum_le_sum (fun k _ => hg_bd _)
      _ = 2 * ((Finset.univ.filter
            (fun k : Fin K => |lam k - (-(2 * Real.pi * ξ))| ≤ (scaleT j)⁻¹)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 2 * 2 := by
          have hcast : ((Finset.univ.filter
              (fun k : Fin K => |lam k - (-(2 * Real.pi * ξ))| ≤ (scaleT j)⁻¹)).card : ℝ) ≤ 2 := by
            exact_mod_cast hS
          linarith
      _ = 4 := by norm_num
  have hZ : (2:ℂ) * (Real.pi:ℂ) * (∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k))))
      = ((2 * Real.pi : ℝ) : ℂ) * (∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k)))) := by
    push_cast; ring
  calc ‖2 * Real.pi * ∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k)))‖
      = 2 * Real.pi * ‖∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k)))‖ := by
        rw [hZ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    _ ≤ 2 * Real.pi * 4 := by
        have h2 : (0:ℝ) ≤ 2 * Real.pi := by positivity
        exact mul_le_mul_of_nonneg_left hsum h2
    _ = 8 * Real.pi := by ring

lemma xiMul_memLp {K : ℕ} {lam : Fin K → ℝ} {g : ℝ → ℂ} (hg : Measurable g)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (j : ℕ) :
    MemLp (xiMul g lam j) ⊤ (volume : Measure ℝ) := by
  refine memLp_top_of_bound ?_ (8 * Real.pi) ?_
  · exact (Measurable.const_mul (Finset.measurable_sum _ (fun k _ =>
      hg.comp (by fun_prop : Measurable (fun ξ : ℝ => -(scaleT j * (2 * Real.pi * ξ + lam k)))))) _).aestronglyMeasurable
  · filter_upwards with ξ
    exact xiMul_bound hsep hg_supp hg_bd ξ j

/-- At most one dyadic scale contributes at a given frequency `ξ`. -/
lemma xi_at_most_one_scale {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {g : ℝ → ℂ}
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (ξ : ℝ) {j j' : ℕ}
    (hj : ∃ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k))) ≠ 0)
    (hj' : ∃ k : Fin K, g (-(scaleT j' * (2 * Real.pi * ξ + lam k))) ≠ 0) : j = j' := by
  have hsm : StrictMono (fun n : ℕ => (2:ℝ)^n) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self n)
  obtain ⟨k, hk⟩ := hj
  obtain ⟨k', hk'⟩ := hj'
  have hb : ∀ (m : ℕ) (l : Fin K), g (-(scaleT m * (2 * Real.pi * ξ + lam l))) ≠ 0 →
      1/2 < scaleT m * |2 * Real.pi * ξ + lam l| ∧ scaleT m * |2 * Real.pi * ξ + lam l| ≤ 1 := by
    intro m l hl
    have hcon : 1/2 < |(-(scaleT m * (2 * Real.pi * ξ + lam l)))| ∧
        |(-(scaleT m * (2 * Real.pi * ξ + lam l)))| ≤ 1 := by
      by_contra hc
      exact hl (hg_supp _ hc)
    rw [abs_neg, abs_mul, abs_of_pos (scaleT_pos m)] at hcon
    exact hcon
  obtain ⟨hk1, hk2⟩ := hb j k hk
  obtain ⟨hk1', hk2'⟩ := hb j' k' hk'
  have htj : (0:ℝ) < scaleT j := scaleT_pos j
  have htj' : (0:ℝ) < scaleT j' := scaleT_pos j'
  have hu2 : |2 * Real.pi * ξ + lam k| ≤ (scaleT j)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ htj]; nlinarith [hk2]
  have hu2' : |2 * Real.pi * ξ + lam k'| ≤ (scaleT j')⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ htj']; nlinarith [hk2']
  have hu1 : (scaleT j)⁻¹ / 2 < |2 * Real.pi * ξ + lam k| := by
    have h := mul_lt_mul_of_pos_left hk1 (inv_pos.mpr htj)
    have h' : (scaleT j)⁻¹ * (scaleT j * |2 * Real.pi * ξ + lam k|) = |2 * Real.pi * ξ + lam k| := by
      rw [← mul_assoc, inv_mul_cancel₀ htj.ne', one_mul]
    rw [h'] at h
    calc (scaleT j)⁻¹ / 2 = (scaleT j)⁻¹ * (1/2) := by ring
      _ < |2 * Real.pi * ξ + lam k| := h
  have hu1' : (scaleT j')⁻¹ / 2 < |2 * Real.pi * ξ + lam k'| := by
    have h := mul_lt_mul_of_pos_left hk1' (inv_pos.mpr htj')
    have h' : (scaleT j')⁻¹ * (scaleT j' * |2 * Real.pi * ξ + lam k'|) = |2 * Real.pi * ξ + lam k'| := by
      rw [← mul_assoc, inv_mul_cancel₀ htj'.ne', one_mul]
    rw [h'] at h
    calc (scaleT j')⁻¹ / 2 = (scaleT j')⁻¹ * (1/2) := by ring
      _ < |2 * Real.pi * ξ + lam k'| := h
  rcases eq_or_ne k k' with hkk | hkk
  · -- same frequency: `t_j/2 < t_{j'} < 2 t_j`, and both are powers of `2` `≥ 2`
    subst hkk
    have hlt : (scaleT j)⁻¹ / 2 < (scaleT j')⁻¹ := by linarith [hu1, hu2']
    have hlt2 : (scaleT j')⁻¹ / 2 < (scaleT j)⁻¹ := by linarith [hu1', hu2]
    have hA : scaleT j' < 2 * scaleT j := by
      have h : (2 * scaleT j)⁻¹ < (scaleT j')⁻¹ := by
        rw [show (2 * scaleT j)⁻¹ = (scaleT j)⁻¹ / 2 by field_simp]
        exact hlt
      exact (inv_lt_inv₀ (a := 2 * scaleT j) (b := scaleT j') (by positivity) (scaleT_pos j')).mp h
    have hB : scaleT j < 2 * scaleT j' := by
      have h : (2 * scaleT j')⁻¹ < (scaleT j)⁻¹ := by
        rw [show (2 * scaleT j')⁻¹ = (scaleT j')⁻¹ / 2 by field_simp]
        exact hlt2
      exact (inv_lt_inv₀ (a := 2 * scaleT j') (b := scaleT j) (by positivity) (scaleT_pos j)).mp h
    have hA' : (2:ℝ)^(j'+1) < (2:ℝ)^(j+1+1) := by
      have h2 : (2:ℝ)^(j+1+1) = 2 * scaleT j := by rw [scaleT, pow_succ]; ring
      rw [h2]; exact hA
    have hB' : (2:ℝ)^(j+1) < (2:ℝ)^(j'+1+1) := by
      have h2 : (2:ℝ)^(j'+1+1) = 2 * scaleT j' := by rw [scaleT, pow_succ]; ring
      rw [h2]; exact hB
    have h1 : j' + 1 < j + 1 + 1 := hsm.lt_iff_lt.mp hA'
    have h2 : j + 1 < j' + 1 + 1 := hsm.lt_iff_lt.mp hB'
    omega
  · -- different frequencies: `t_j = t_{j'} = 2`
    have h1 : (1:ℝ) ≤ |lam k - lam k'| := hsep k k' hkk
    have h2 : |lam k - lam k'| ≤ |2 * Real.pi * ξ + lam k| + |2 * Real.pi * ξ + lam k'| := by
      have h := abs_sub_le (2 * Real.pi * ξ + lam k) 0 (2 * Real.pi * ξ + lam k')
      simp only [sub_zero, zero_sub, abs_neg] at h
      have heq : (2 * Real.pi * ξ + lam k) - (2 * Real.pi * ξ + lam k') = lam k - lam k' := by ring
      rw [heq] at h
      exact h
    have h4 : (scaleT j)⁻¹ ≤ 1/2 := scaleT_inv_le_half j
    have h5 : (scaleT j')⁻¹ ≤ 1/2 := scaleT_inv_le_half j'
    have h3 : (scaleT j)⁻¹ + (scaleT j')⁻¹ ≤ 1 := by linarith
    have h6 : (1:ℝ) ≤ (scaleT j)⁻¹ + (scaleT j')⁻¹ := by linarith [h1, h2, hu2, hu2']
    have h7 : (scaleT j)⁻¹ = 1/2 := by linarith
    have h8 : (scaleT j')⁻¹ = 1/2 := by linarith
    have hj2 : scaleT j = 2 := by
      rw [← inv_inv (scaleT j), h7]; norm_num
    have hj'2 : scaleT j' = 2 := by
      rw [← inv_inv (scaleT j'), h8]; norm_num
    have : j + 1 = j' + 1 := hsm.injective (by rw [← scaleT, ← scaleT]; rw [hj2, hj'2])
    omega

lemma xiMul_tsum_le {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {g : ℝ → ℂ} (hg : Measurable g)
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (ξ : ℝ) :
    (∑' j : ℕ, ‖xiMul g lam j ξ‖ₑ ^ (2:ℝ)) ≤ ENNReal.ofReal ((8 * Real.pi)^2) := by
  by_cases h : ∃ j : ℕ, xiMul g lam j ξ ≠ 0
  · obtain ⟨j0, hj0⟩ := h
    have hne : ∃ k : Fin K, g (-(scaleT j0 * (2 * Real.pi * ξ + lam k))) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hj0 (by rw [xiMul, Finset.sum_congr rfl (fun k _ => hc k), Finset.sum_const_zero, mul_zero])
    have hzero : ∀ j : ℕ, j ≠ j0 → xiMul g lam j ξ = 0 := by
      intro j hj
      by_contra hc
      have hk : ∃ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k))) ≠ 0 := by
        by_contra hcc
        push Not at hcc
        exact hc (by rw [xiMul, Finset.sum_congr rfl (fun k _ => hcc k), Finset.sum_const_zero, mul_zero])
      exact hj (xi_at_most_one_scale hsep hg_supp ξ hk hne)
    rw [tsum_eq_single j0 (fun j hj => by rw [hzero j hj]; simp)]
    have hb : ‖xiMul g lam j0 ξ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal ((8 * Real.pi)^2) := by
      have h1 : ‖xiMul g lam j0 ξ‖ₑ ≤ ENNReal.ofReal (8 * Real.pi) := by
        rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
        exact ENNReal.ofReal_le_ofReal (xiMul_bound hsep hg_supp hg_bd ξ j0)
      calc ‖xiMul g lam j0 ξ‖ₑ ^ (2:ℝ)
          ≤ (ENNReal.ofReal (8 * Real.pi)) ^ (2:ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
        _ = ENNReal.ofReal ((8 * Real.pi)^2) := by
            rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity)]
    exact hb
  · push Not at h
    simp [h]

/-! ### The `K = 1` case of the fixed-window maximal estimate

The simplest instance of the crux: for a *single* function the maximal band-pass operator is
bounded by an absolute constant, because the family `h_j Ψ(h_j ·)` is a sub-family of the full
dilation family `t⁻¹ • Ψ(·/t)`, `t > 0`, whose maximal function is the published
`maximal_dilation_convolution_l2`.  (This is the `K = 1` piece of Bourgain's Lemma 4.13; the
`K`-dependence is the genuine content.) -/

noncomputable def winKc (Ψ : SchwartzMap ℝ ℂ) (j : ℕ) : ℝ → ℂ :=
  fun u => (((2:ℝ)^(-(j:ℝ)-1) : ℝ) : ℂ) * (Ψ ((2:ℝ)^(-(j:ℝ)-1) * u))
/-! ### Bourgain's geometric bootstrap (the iteration half of the crux)

`iterate_bound` is the iteration engine of the fixed-window maximal estimate: given
* the **one-step** inequality `bandMax H ≤ A · bandSq H + bandMax (H - T_y H)` (a fixed shift `y`),
* the **contraction** `bandSq (H - T_y H) ≤ ρ · bandSq H` for that same `y`,
* the **a priori bound** `bandMax H ≤ CK · bandSq H`,
the maximal estimate follows with the geometric constant `A/(1-ρ)`.  Everything in this lemma is
elementary `ℝ≥0∞` arithmetic; the content of the crux is the *one-step* inequality, whose two
inputs are the published entropy chain and the published translation contraction. -/

/-- **Geometric iteration (Bourgain's bootstrap).**  If
`M n ≤ A · S n + M (n+1)`, `S (n+1) ≤ ρ · S n`, `M n ≤ CK · S n` and `S 0 < ∞`, then
`M 0 ≤ A/(1-ρ) · S 0`. -/
theorem iterate_bound {M S : ℕ → ℝ≥0∞} {A ρ CK : ℝ}
    (hA : 0 ≤ A) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hCK : 0 ≤ CK) (hfin : S 0 < ⊤)
    (hrec : ∀ n, M n ≤ ENNReal.ofReal A * S n + M (n+1))
    (hSdec : ∀ n, S (n+1) ≤ ENNReal.ofReal ρ * S n)
    (htail : ∀ n, M n ≤ ENNReal.ofReal CK * S n) :
    M 0 ≤ ENNReal.ofReal (A / (1 - ρ)) * S 0 := by
  have hpow_le_one : ∀ n, (ENNReal.ofReal ρ) ^ n ≤ 1 := fun n =>
    pow_le_one₀ (by simp) (by rw [ENNReal.ofReal_le_one]; linarith)
  have hSpow : ∀ n, S n ≤ (ENNReal.ofReal ρ) ^ n * S 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc S (n+1) ≤ ENNReal.ofReal ρ * S n := hSdec n
          _ ≤ ENNReal.ofReal ρ * ((ENNReal.ofReal ρ) ^ n * S 0) := mul_le_mul_right ih _
          _ = (ENNReal.ofReal ρ) ^ (n+1) * S 0 := by ring
  have hSn_fin : ∀ n, S n < ⊤ := fun n =>
    lt_of_le_of_lt (le_trans (hSpow n) (by
      simpa using mul_le_mul_left (hpow_le_one n) (S 0))) hfin
  have hsum : ∀ n, M 0 ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * S i) + M n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc M 0 ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * S i) + M n := ih
          _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * S i)
                + (ENNReal.ofReal A * S n + M (n+1)) := add_le_add_right (hrec n) _
          _ = (∑ i ∈ Finset.range n, ENNReal.ofReal A * S i) + ENNReal.ofReal A * S n + M (n+1) := by
              ring
          _ = (∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * S i) + M (n+1) := by
              rw [Finset.sum_range_succ]
  have hcast : ∀ n, (∑ i ∈ Finset.range n, ENNReal.ofReal A * S i) + M n
      ≤ ENNReal.ofReal (A * (∑ i ∈ Finset.range n, ρ ^ i) + CK * ρ ^ n) * S 0 := by
    intro n
    have h1 : (∑ i ∈ Finset.range n, ENNReal.ofReal A * S i)
        ≤ ENNReal.ofReal (A * (∑ i ∈ Finset.range n, ρ ^ i)) * S 0 := by
      calc (∑ i ∈ Finset.range n, ENNReal.ofReal A * S i)
          = ENNReal.ofReal A * (∑ i ∈ Finset.range n, S i) := (Finset.mul_sum _ _ _).symm
        _ ≤ ENNReal.ofReal A * (∑ i ∈ Finset.range n, (ENNReal.ofReal ρ) ^ i * S 0) :=
            mul_le_mul_right (Finset.sum_le_sum (fun i _ => hSpow i)) _
        _ = ENNReal.ofReal A * ((∑ i ∈ Finset.range n, (ENNReal.ofReal ρ) ^ i) * S 0) := by
            rw [Finset.sum_mul]
        _ = ENNReal.ofReal A * (ENNReal.ofReal (∑ i ∈ Finset.range n, ρ ^ i) * S 0) := by
            rw [show (∑ i ∈ Finset.range n, (ENNReal.ofReal ρ) ^ i)
                = ENNReal.ofReal (∑ i ∈ Finset.range n, ρ ^ i) from by
              rw [show (∑ i ∈ Finset.range n, (ENNReal.ofReal ρ) ^ i)
                  = ∑ i ∈ Finset.range n, ENNReal.ofReal (ρ ^ i) from
                Finset.sum_congr rfl (fun i _ => (ENNReal.ofReal_pow hρ0 i).symm),
                ← ENNReal.ofReal_sum_of_nonneg (fun i _ => pow_nonneg hρ0 i)]]
        _ = ENNReal.ofReal (A * (∑ i ∈ Finset.range n, ρ ^ i)) * S 0 := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hA]
    have h2 : M n ≤ ENNReal.ofReal (CK * ρ ^ n) * S 0 := by
      calc M n ≤ ENNReal.ofReal CK * S n := htail n
        _ ≤ ENNReal.ofReal CK * ((ENNReal.ofReal ρ) ^ n * S 0) := mul_le_mul_right (hSpow n) _
        _ = ENNReal.ofReal CK * (ENNReal.ofReal (ρ ^ n) * S 0) := by
            rw [ENNReal.ofReal_pow hρ0 n]
        _ = ENNReal.ofReal (CK * ρ ^ n) * S 0 := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hCK]
    calc (∑ i ∈ Finset.range n, ENNReal.ofReal A * S i) + M n
        ≤ ENNReal.ofReal (A * (∑ i ∈ Finset.range n, ρ ^ i)) * S 0
          + ENNReal.ofReal (CK * ρ ^ n) * S 0 := add_le_add h1 h2
      _ = (ENNReal.ofReal (A * (∑ i ∈ Finset.range n, ρ ^ i)) + ENNReal.ofReal (CK * ρ ^ n)) * S 0 := by
          ring
      _ = ENNReal.ofReal (A * (∑ i ∈ Finset.range n, ρ ^ i) + CK * ρ ^ n) * S 0 := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  -- the real sequence converges to `A/(1-ρ)`
  have hgeosum : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, ρ ^ i) atTop (𝓝 ((1 - ρ)⁻¹)) :=
    (hasSum_geometric_of_lt_one hρ0 hρ1).tendsto_sum_nat
  have hlim : Tendsto (fun n : ℕ => A * (∑ i ∈ Finset.range n, ρ ^ i) + CK * ρ ^ n) atTop
      (𝓝 (A / (1 - ρ))) := by
    have h1 := hgeosum.const_mul A
    have h2 : Tendsto (fun n : ℕ => CK * ρ ^ n) atTop (𝓝 (CK * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul CK
    simpa only [mul_zero, add_zero, div_eq_mul_inv] using h1.add h2
  -- conclude
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  by_cases hS0zero : S 0 = 0
  · have h := le_trans (hsum 0) (hcast 0)
    simp only [Finset.range_zero, Finset.sum_empty, zero_add] at h
    rw [hS0zero, mul_zero] at h
    exact le_trans h (by simp)
  · have hS0pos : 0 < (S 0).toReal := ENNReal.toReal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr hS0zero, hfin⟩
    set δ : ℝ := ε.toReal / (S 0).toReal with hδ
    have hεpos : 0 < (ε : ℝ≥0∞).toReal := ENNReal.toReal_pos_iff.mpr
      ⟨bot_lt_iff_ne_bot.mpr (by simp [hε.ne']), ENNReal.coe_lt_top (r := ε)⟩
    have hδpos : 0 < δ := div_pos hεpos hS0pos
    have hδε : ENNReal.ofReal δ * S 0 ≤ ε := by
      have h1 : ENNReal.ofReal δ * S 0 = ENNReal.ofReal (δ * (S 0).toReal) := by
        conv_lhs => rw [← ENNReal.ofReal_toReal hfin.ne]
        rw [← ENNReal.ofReal_mul hδpos.le]
      rw [h1, show δ * (S 0).toReal = ε.toReal by rw [hδ]; field_simp]
      rw [show ε.toReal = (ε : ℝ) by simp]
      exact le_of_eq ENNReal.ofReal_coe_nnreal
    have hev : ∀ᶠ n : ℕ in atTop,
        A * (∑ i ∈ Finset.range n, ρ ^ i) + CK * ρ ^ n ≤ A / (1 - ρ) + δ :=
      (hlim.eventually (eventually_lt_nhds (by linarith))).mono (fun n hn => le_of_lt hn)
    obtain ⟨n, hn⟩ := hev.exists
    refine le_trans (le_iInf (fun m => le_trans (hsum m) (hcast m)) : M 0 ≤ _) ?_
    calc (⨅ m, ENNReal.ofReal (A * (∑ i ∈ Finset.range m, ρ ^ i) + CK * ρ ^ m) * S 0)
        ≤ ENNReal.ofReal (A * (∑ i ∈ Finset.range n, ρ ^ i) + CK * ρ ^ n) * S 0 := iInf_le _ n
      _ ≤ ENNReal.ofReal (A / (1 - ρ) + δ) * S 0 := mul_le_mul_left (ENNReal.ofReal_le_ofReal hn) _
      _ ≤ (ENNReal.ofReal (A / (1 - ρ)) + ENNReal.ofReal δ) * S 0 := by
          refine mul_le_mul_left ?_ _
          rw [ENNReal.ofReal_add (by positivity) hδpos.le]
      _ = ENNReal.ofReal (A / (1 - ρ)) * S 0 + ENNReal.ofReal δ * S 0 := by ring
      _ ≤ ENNReal.ofReal (A / (1 - ρ)) * S 0 + ε := add_le_add_right hδε _

end

end Commons.Analysis.Fourier

