import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Commons.Analysis.Integral.intervalIntegral_comp_norm_le

open MeasureTheory Set
open scoped BigOperators

namespace Commons.Analysis.Integral

/-- Every coordinate of a vector in `EuclideanSpace ℝ (Fin N)` has norm at most the norm of the
vector. -/
lemma euclideanSpace_norm_apply_le {N : ℕ} (z : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    ‖z i‖ ≤ ‖z‖ := by
  have h := EuclideanSpace.norm_sq_eq z
  have hle : ‖z i‖ ^ 2 ≤ ∑ j : Fin N, ‖z j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  have h2 : ‖z i‖ ^ 2 ≤ ‖z‖ ^ 2 := by rw [h]; exact hle
  nlinarith [norm_nonneg (z i), norm_nonneg z]

/-- Comparison of integrals of `t⁻¹` over positive intervals: if `0 < a ≤ b`, `0 < c ≤ d` with
`c ≤ a` and `b ≤ d` then `∫_a^b t⁻¹ ≤ ∫_c^d t⁻¹`. -/
lemma intervalIntegral_inv_le_of_le {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (hca : c ≤ a) (hbd : b ≤ d) :
    ∫ t in a..b, t⁻¹ ≤ ∫ t in c..d, t⁻¹ := by
  have h0ab : (0:ℝ) ∉ Set.uIcc a b := by
    rw [Set.mem_uIcc]; rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> linarith
  have h0cd : (0:ℝ) ∉ Set.uIcc c d := by
    rw [Set.mem_uIcc]; rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> linarith
  rw [integral_inv h0ab, integral_inv h0cd]
  apply Real.log_le_log (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- If `0 ≤ inner ℝ q e` then `‖q‖ ≤ ‖q + T • e‖` for `0 ≤ T`. -/
lemma norm_le_norm_add_smul_of_cos {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {q e : E} {T : ℝ} (hT : 0 ≤ T) (hcos0 : 0 ≤ inner ℝ q e) :
    ‖q‖ ≤ ‖q + T • e‖ := by
  have h : ‖q‖ ^ 2 ≤ ‖q + T • e‖ ^ 2 := by
    rw [norm_add_sq_real]
    have h1 : 0 ≤ inner ℝ q (T • e) := by
      rw [real_inner_smul_right]; exact mul_nonneg hT hcos0
    nlinarith [sq_nonneg ‖T • e‖]
  nlinarith [norm_nonneg q, norm_nonneg (q + T • e)]

/-- **Per-pair integral estimate.**  If `q, e` satisfy the angle lower bound `(1/2)‖q‖‖e‖ ≤
⟪q, e⟫` (so that `q + s • e` never vanishes for `s ≥ 0`) and `ν` is a positive lower bound for
`‖q‖` and `‖e‖`, then
`∫_0^T ‖q + s • e‖⁻¹ ds ≤ 2 ν⁻¹ ∫_ν^M t⁻¹ dt`
whenever `‖q + T • e‖ ≤ M`. -/
theorem integral_inv_norm_add_smul_le_inv_mul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {q e : E} {ν M : ℝ} (hν : 0 < ν) (he : ν ≤ ‖e‖) (hq : ν ≤ ‖q‖)
    (hcos : (1/2) * (‖q‖ * ‖e‖) ≤ inner ℝ q e) {T : ℝ} (hT : 0 ≤ T)
    (hM : ‖q + T • e‖ ≤ M) :
    ∫ s in (0:ℝ)..T, (‖q + s • e‖)⁻¹ ≤ 2 * ν⁻¹ * ∫ t in ν..M, t⁻¹ := by
  have hepos : 0 < ‖e‖ := lt_of_lt_of_le hν he
  have hqpos : 0 < ‖q‖ := lt_of_lt_of_le hν hq
  have hangle : 0 ≤ inner ℝ q e :=
    le_trans (mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hcos
  have hmono : ‖q‖ ≤ ‖q + T • e‖ := norm_le_norm_add_smul_of_cos hT hangle
  have hbT : 0 < ‖q + T • e‖ := lt_of_lt_of_le hqpos hmono
  have hMpos : 0 < M := lt_of_lt_of_le hbT hM
  have hf : ∀ t : ℝ, 0 ≤ (|t|)⁻¹ := fun t => inv_nonneg.mpr (abs_nonneg t)
  have hfm : Measurable (fun t : ℝ => (|t|)⁻¹) := measurable_inv.comp measurable_abs
  have hcomp := intervalIntegral_comp_norm_le (q := q) (e := e) (c := (1/2)) hepos
    (by norm_num) (by norm_num) hcos hf hfm hT
  have hL : ∫ s in (0:ℝ)..T, (|‖q + s • e‖|)⁻¹ = ∫ s in (0:ℝ)..T, (‖q + s • e‖)⁻¹ :=
    intervalIntegral.integral_congr (fun s _ => by
      show |‖q + s • e‖|⁻¹ = ‖q + s • e‖⁻¹
      rw [abs_of_nonneg (norm_nonneg _)])
  have hR : ∫ t in ‖q‖..‖q + T • e‖, (|t|)⁻¹ = ∫ t in ‖q‖..‖q + T • e‖, t⁻¹ := by
    apply intervalIntegral.integral_congr
    intro t ht
    have h1 : ‖q‖ ≤ t := by
      rcases (Set.mem_uIcc.mp ht) with ⟨h3, _⟩ | ⟨h3, _⟩
      · exact h3
      · exact le_trans hmono h3
    have htpos : 0 < t := lt_of_lt_of_le hqpos h1
    show |t|⁻¹ = t⁻¹
    rw [abs_of_pos htpos]
  rw [hL, hR] at hcomp
  have hIle : ∫ t in ‖q‖..‖q + T • e‖, t⁻¹ ≤ ∫ t in ν..M, t⁻¹ :=
    intervalIntegral_inv_le_of_le hqpos hbT hν hMpos hq hM
  have hInn : 0 ≤ ∫ t in ‖q‖..‖q + T • e‖, t⁻¹ :=
    intervalIntegral.integral_nonneg hmono (fun u hu => inv_nonneg.mpr (le_trans hqpos.le hu.1))
  have hinv : ‖e‖⁻¹ ≤ ν⁻¹ := inv_anti₀ hν he
  have h1 : (1/2:ℝ)⁻¹ = 2 := by norm_num
  rw [h1] at hcomp
  calc ∫ s in (0:ℝ)..T, (‖q + s • e‖)⁻¹
      ≤ 2 * (‖e‖⁻¹ * ∫ t in ‖q‖..‖q + T • e‖, t⁻¹) := hcomp
    _ ≤ 2 * (ν⁻¹ * ∫ t in ‖q‖..‖q + T • e‖, t⁻¹) := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hinv hInn)
          (by norm_num : (0:ℝ) ≤ 2)
        linarith
    _ ≤ 2 * (ν⁻¹ * ∫ t in ν..M, t⁻¹) := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIle (inv_nonneg.mpr hν.le))
          (by norm_num : (0:ℝ) ≤ 2)
        linarith
    _ = 2 * ν⁻¹ * ∫ t in ν..M, t⁻¹ := by ring

/-- Interval integrability of `s ↦ ‖q + s • e‖⁻¹` under the angle lower bound. -/
lemma intervalIntegrable_inv_norm_add_smul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {q e : E} {ν : ℝ} (hν : 0 < ν) (he : ν ≤ ‖e‖) (hq : ν ≤ ‖q‖)
    (hcos : (1/2) * (‖q‖ * ‖e‖) ≤ inner ℝ q e) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun s : ℝ => (‖q + s • e‖)⁻¹) volume 0 T := by
  have hepos : 0 < ‖e‖ := lt_of_lt_of_le hν he
  have hne : ∀ s ∈ Set.Icc (0:ℝ) T, q + s • e ≠ 0 := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h0 | hpos
    · rw [← h0, zero_smul, add_zero]
      exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hν hq))
    · exact add_smul_ne_zero_of_cos hepos (by norm_num) hcos hpos
  have hcont : ContinuousOn (fun s : ℝ => ‖q + s • e‖) (Set.Icc (0:ℝ) T) := by
    apply Continuous.continuousOn
    fun_prop
  refine (hcont.inv₀ (fun s hs => ?_)).intervalIntegrable_of_Icc hT
  exact norm_ne_zero_iff.mpr (hne s hs)

/-- Combinatorial counting bound: the sum over pairs `i < j` of the constant `2c` (`c ≥ 0`) is at
most `N² c`. -/
lemma sum_Iio_two_mul_le (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (∑ j : Fin N, ∑ _i ∈ Finset.Iio j, 2 * c) ≤ (N : ℝ) ^ 2 * c := by
  have hS2 : (∑ j : Fin N, ((j : ℕ) : ℝ)) * 2 = ((N * (N - 1) : ℕ) : ℝ) := by
    have h : (∑ j : Fin N, ((j : ℕ) : ℝ)) = ((∑ i ∈ Finset.range N, i : ℕ) : ℝ) := by
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (i : ℝ))]
      push_cast
      ring
    rw [h]
    exact_mod_cast Finset.sum_range_id_mul_two N
  have hle : ((N * (N - 1) : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
    have h1 : N * (N - 1) ≤ N * N := Nat.mul_le_mul_left N (Nat.sub_le N 1)
    calc ((N * (N - 1) : ℕ) : ℝ) ≤ ((N * N : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (N : ℝ) ^ 2 := by push_cast; ring
  calc (∑ j : Fin N, ∑ _i ∈ Finset.Iio j, 2 * c)
      = (∑ j : Fin N, ((Finset.Iio j).card : ℝ)) * (2 * c) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (∑ j : Fin N, ((j : ℕ) : ℝ)) * (2 * c) := by
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [Fin.card_Iio]
    _ = ((N * (N - 1) : ℕ) : ℝ) * c := by rw [← mul_assoc, hS2]
    _ ≤ (N : ℝ) ^ 2 * c := mul_le_mul_of_nonneg_right hle hc

theorem integral_pairSum_inv_le_of_separated {N : ℕ} (hN : 2 ≤ N)
    (z a : EuclideanSpace ℝ (Fin N)) {ν : ℝ} (hν : 0 < ν)
    (ha : ‖a‖ = 1) (hsepa : ∀ i j, i ≠ j → ν ≤ ‖a i - a j‖)
    (hsepz : ∀ i j, i ≠ j → ν ≤ ‖z i - z j‖)
    (hangle : ∀ i j, i ≠ j → (1 / 2) * (‖z i - z j‖ * ‖a i - a j‖) ≤ inner ℝ (z i - z j) (a i - a j))
    {T : ℝ} (hT : 0 ≤ T) :
    ∫ s in (0:ℝ)..T, ∑ j, ∑ i ∈ Finset.Iio j, (‖(z i - z j) + s • (a i - a j)‖)⁻¹
      ≤ (N:ℝ)^2 * (ν⁻¹ * ∫ t in ν..(2 * T + 2 * ‖z‖), t⁻¹) := by
  set M : ℝ := 2 * T + 2 * ‖z‖ with hMdef
  have hzi : ∀ i : Fin N, ‖z i‖ ≤ ‖z‖ := fun i => euclideanSpace_norm_apply_le z i
  have hai : ∀ i : Fin N, ‖a i‖ ≤ 1 := by
    intro i
    have := euclideanSpace_norm_apply_le a i
    rwa [ha] at this
  have hbound : ∀ i j : Fin N, i ≠ j → ‖(z i - z j) + T • (a i - a j)‖ ≤ M := by
    intro i j _
    calc ‖(z i - z j) + T • (a i - a j)‖
        ≤ ‖z i - z j‖ + ‖T • (a i - a j)‖ := norm_add_le _ _
      _ = ‖z i - z j‖ + T * ‖a i - a j‖ := by rw [norm_smul, Real.norm_of_nonneg hT]
      _ ≤ (‖z‖ + ‖z‖) + T * (1 + 1) := by
            have h1 : ‖z i - z j‖ ≤ ‖z‖ + ‖z‖ :=
              le_trans (norm_sub_le _ _) (add_le_add (hzi i) (hzi j))
            have h2 : ‖a i - a j‖ ≤ 1 + 1 :=
              le_trans (norm_sub_le _ _) (add_le_add (hai i) (hai j))
            have h3 : T * ‖a i - a j‖ ≤ T * (1 + 1) := mul_le_mul_of_nonneg_left h2 hT
            linarith
      _ = M := by rw [hMdef]; ring
  have hpair : ∀ j : Fin N, ∀ i ∈ Finset.Iio j,
      ∫ s in (0:ℝ)..T, (‖(z i - z j) + s • (a i - a j)‖)⁻¹
        ≤ 2 * (ν⁻¹ * ∫ t in ν..M, t⁻¹) := by
    intro j i hi
    have hij : i ≠ j := ne_of_lt (Finset.mem_Iio.mp hi)
    have := integral_inv_norm_add_smul_le_inv_mul (q := z i - z j) (e := a i - a j)
      hν (hsepa i j hij) (hsepz i j hij) (hangle i j hij) hT (hbound i j hij)
    simpa only [mul_assoc] using this
  have hInt : ∀ i j : Fin N, i ≠ j →
      IntervalIntegrable (fun s : ℝ => (‖(z i - z j) + s • (a i - a j)‖)⁻¹) volume 0 T :=
    fun i j hij =>
      intervalIntegrable_inv_norm_add_smul hν (hsepa i j hij) (hsepz i j hij) (hangle i j hij) hT
  have hsplit : ∫ s in (0:ℝ)..T, (∑ j : Fin N, ∑ i ∈ Finset.Iio j,
        (‖(z i - z j) + s • (a i - a j)‖)⁻¹)
      = ∑ j : Fin N, ∑ i ∈ Finset.Iio j,
          ∫ s in (0:ℝ)..T, (‖(z i - z j) + s • (a i - a j)‖)⁻¹ := by
    have h1 : ∫ s in (0:ℝ)..T, (∑ j : Fin N, ∑ i ∈ Finset.Iio j,
          (‖(z i - z j) + s • (a i - a j)‖)⁻¹)
        = ∑ j : Fin N, ∫ s in (0:ℝ)..T, (∑ i ∈ Finset.Iio j,
            (‖(z i - z j) + s • (a i - a j)‖)⁻¹) := by
      refine intervalIntegral.integral_finsetSum (s := Finset.univ) (fun j _ => ?_)
      have hsum := IntervalIntegrable.sum (Finset.Iio j)
        (f := fun i => fun s : ℝ => (‖(z i - z j) + s • (a i - a j)‖)⁻¹)
        (fun i hi => hInt i j (ne_of_lt (Finset.mem_Iio.mp hi)))
      rw [show (fun s : ℝ => ∑ i ∈ Finset.Iio j, (‖(z i - z j) + s • (a i - a j)‖)⁻¹)
            = (∑ i ∈ Finset.Iio j, fun s : ℝ => (‖(z i - z j) + s • (a i - a j)‖)⁻¹) from by
              ext s
              rw [Finset.sum_apply]]
      exact hsum
    have h2 : ∀ j : Fin N, (∫ s in (0:ℝ)..T, (∑ i ∈ Finset.Iio j,
          (‖(z i - z j) + s • (a i - a j)‖)⁻¹))
        = ∑ i ∈ Finset.Iio j, ∫ s in (0:ℝ)..T, (‖(z i - z j) + s • (a i - a j)‖)⁻¹ := by
      intro j
      refine intervalIntegral.integral_finsetSum (fun i hi => ?_)
      exact hInt i j (ne_of_lt (Finset.mem_Iio.mp hi))
    rw [h1, Finset.sum_congr rfl (fun j _ => h2 j)]
  rw [hsplit]
  have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp
  have hνM : ν ≤ M := by
    have h1 : ν ≤ ‖z ⟨0, by omega⟩ - z ⟨1, by omega⟩‖ := hsepz _ _ h01
    have h2 : ‖z ⟨0, by omega⟩ - z ⟨1, by omega⟩‖ ≤ 2 * ‖z‖ := by
      calc ‖z ⟨0, by omega⟩ - z ⟨1, by omega⟩‖
          ≤ ‖z ⟨0, by omega⟩‖ + ‖z ⟨1, by omega⟩‖ := norm_sub_le _ _
        _ ≤ ‖z‖ + ‖z‖ := add_le_add (hzi _) (hzi _)
        _ = 2 * ‖z‖ := by ring
    have h3 : 2 * ‖z‖ ≤ M := by rw [hMdef]; linarith
    linarith
  have hInn : 0 ≤ ∫ t in ν..M, t⁻¹ :=
    intervalIntegral.integral_nonneg hνM (fun u hu => inv_nonneg.mpr (le_trans hν.le hu.1))
  have hc : 0 ≤ ν⁻¹ * ∫ t in ν..M, t⁻¹ := mul_nonneg (inv_nonneg.mpr hν.le) hInn
  calc ∑ j : Fin N, ∑ i ∈ Finset.Iio j,
        ∫ s in (0:ℝ)..T, (‖(z i - z j) + s • (a i - a j)‖)⁻¹
      ≤ ∑ j : Fin N, ∑ i ∈ Finset.Iio j, 2 * (ν⁻¹ * ∫ t in ν..M, t⁻¹) :=
          Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i hi => hpair j i hi))
    _ ≤ (N:ℝ)^2 * (ν⁻¹ * ∫ t in ν..M, t⁻¹) := sum_Iio_two_mul_le N _ hc
    _ = (N:ℝ)^2 * (ν⁻¹ * ∫ t in ν..(2 * T + 2 * ‖z‖), t⁻¹) := by rw [hMdef]

end Commons.Analysis.Integral