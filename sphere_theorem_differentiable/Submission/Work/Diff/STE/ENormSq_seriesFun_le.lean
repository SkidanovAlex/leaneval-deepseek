import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.pd_seriesFun
import Submission.Work.Diff.STE.integral_seriesFun_mul_conj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ENormSq_seriesFun_le`: the physical energy of a Fourier series is controlled by `CSq`

For a coefficient family `c : (ι → ℤ) → ℂ` decaying faster than every polynomial weight
(`∀ N, Summable (fun k => ⟨k⟩^N * ‖c k‖)`), the series `seriesFun c x = Σ_k c k · exp(2πi k·x)`
is smooth, and the `Hᵏ` energy

  `ENormSq k (seriesFun c) = Σ_{l : Fin k → ι} ∫_{unitCube} ‖∂^l (seriesFun c)‖²`

is bounded by a constant (depending only on `k` and `ι`) times the weighted `ℓ²`-norm
`CSq k c = Σ_k ⟨k⟩^{2k} ‖c k‖²`.

This is the bridge between the physical-space energy estimates and the coefficient estimates of
Layer A of the STE development.  The three ingredients are:

* `dmulV l c` (this file): the coefficient family of the iterated derivative `pdList l`, i.e.
  multiplication of the `k`-th coefficient by `∏_{i ∈ l} 2πi kᵢ`;
* `pdList_seriesFun` (sibling file): `pdList l (seriesFun c) = seriesFun (dmulV l c)`;
* `ens_integral_normSq_seriesFun` (sibling file): `∫_{unitCube} ‖seriesFun d‖² = Σ_k ‖d k‖²`;

after which everything is a termwise coefficient inequality: each `|kᵢ|² ≤ ⟨k⟩² = wt k`, so the
`2k`-th order multiplier `∏_{i ∈ l} (2πi kᵢ)` of a list of length `k` has modulus squared at most
`(2π)^{2k} · (wt k)^k`, exactly the weight of `CSq k`.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The iterated Fourier multiplier of a list of derivative directions -/

/-- The coefficient family of the iterated derivative `pdList l`: the `k`-th Fourier coefficient
is multiplied by `∏_{i ∈ l} (2πi kᵢ)`. -/
def dmulV (l : List ι) (c : (ι → ℤ) → ℂ) : (ι → ℤ) → ℂ :=
  fun k => (l.map (fun i => (2 * Real.pi * Complex.I * (k i : ℂ)))).prod * c k

lemma dmulV_nil (c : (ι → ℤ) → ℂ) : dmulV [] c = c := by
  funext k; simp [dmulV]

lemma dmulV_cons (i : ι) (l : List ι) (c : (ι → ℤ) → ℂ) :
    dmulV (i :: l) c = dmul i (dmulV l c) := by
  funext k
  simp only [dmulV, List.map_cons, List.prod_cons, dmul]
  ring

/-! ## Norm bounds for the multiplier -/

private lemma norm_ofReal_mul_I (r : ℝ) : ‖((r : ℂ)) * Complex.I‖ = |r| := by simp

/-- The exact modulus of one multiplier factor `2πi kᵢ`. -/
private lemma norm_dmul_factor (k : ι → ℤ) (i : ι) :
    ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((k i : ℤ) : ℂ)‖
      = 2 * Real.pi * |((k i : ℤ) : ℝ)| := by
  rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((k i : ℤ) : ℂ)
      = (((2 * Real.pi * ((k i : ℤ) : ℝ)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [norm_ofReal_mul_I, abs_mul, abs_mul, abs_of_nonneg Real.pi_nonneg,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

/-- Each coordinate of `k` is dominated by the weight: `kᵢ² ≤ ⟨k⟩²`. -/
lemma sq_le_wt (k : ι → ℤ) (i : ι) : ((k i : ℤ) : ℝ) ^ 2 ≤ wt k := by
  have h := Finset.single_le_sum (f := fun j : ι => ((k j : ℤ) : ℝ) ^ 2)
    (fun j _ => sq_nonneg ((k j : ℤ) : ℝ)) (Finset.mem_univ i)
  simp only [wt]; linarith

/-- The norm of the multiplier `∏_{i ∈ l} (2πi kᵢ)` is at most `(2π ⟨k⟩)^{|l|}`. -/
lemma norm_prod_dmulV_le (l : List ι) (k : ι → ℤ) :
    ‖(l.map (fun i => (2 * Real.pi * Complex.I * (k i : ℂ)))).prod‖
      ≤ (2 * Real.pi * wt k) ^ l.length := by
  have hterm : ∀ i : ι,
      ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((k i : ℤ) : ℂ)‖ ≤ 2 * Real.pi * wt k := by
    intro i
    rw [norm_dmul_factor k i]
    exact mul_le_mul_of_nonneg_left (abs_intCast_le_wt k i) (by positivity)
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    calc ‖(2 * Real.pi * Complex.I * (k i : ℂ))
            * (l.map (fun i => (2 * Real.pi * Complex.I * (k i : ℂ)))).prod‖
        = ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((k i : ℤ) : ℂ)‖
            * ‖(l.map (fun i => (2 * Real.pi * Complex.I * (k i : ℂ)))).prod‖ := norm_mul _ _
      _ ≤ (2 * Real.pi * wt k) * (2 * Real.pi * wt k) ^ l.length :=
          mul_le_mul (hterm i) ih (norm_nonneg _)
            (mul_nonneg (by positivity) (le_of_lt (wt_pos k)))
      _ = (2 * Real.pi * wt k) ^ l.length * (2 * Real.pi * wt k) := by ring

/-- Squared form of the multiplier bound: `∏ (2πi kᵢ)` with `|l| = k` factors has modulus
squared at most `((2π)² ⟨k⟩)^{|l|}`.  This is the sharper bound that consumes exactly the
weight `⟨k⟩^{|l|}` of `CSq`. -/
lemma norm_sq_prod_dmulV_le (l : List ι) (k : ι → ℤ) :
    ‖(l.map (fun i => (2 * Real.pi * Complex.I * (k i : ℂ)))).prod‖ ^ 2
      ≤ ((2 * Real.pi) ^ 2 * wt k) ^ l.length := by
  have hterm : ∀ i : ι,
      ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((k i : ℤ) : ℂ)‖ ^ 2 ≤ (2 * Real.pi) ^ 2 * wt k := by
    intro i
    rw [norm_dmul_factor k i, mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_left (sq_le_wt k i) (sq_nonneg _)
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    calc ‖(2 * Real.pi * Complex.I * (k i : ℂ))
            * (l.map (fun i => (2 * Real.pi * Complex.I * (k i : ℂ)))).prod‖ ^ 2
        = ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((k i : ℤ) : ℂ)‖ ^ 2
            * ‖(l.map (fun i => (2 * Real.pi * Complex.I * (k i : ℂ)))).prod‖ ^ 2 := by
          rw [norm_mul, mul_pow]
      _ ≤ ((2 * Real.pi) ^ 2 * wt k) * (((2 * Real.pi) ^ 2 * wt k) ^ l.length) :=
          mul_le_mul (hterm i) ih (sq_nonneg _)
            (mul_nonneg (sq_nonneg _) (le_of_lt (wt_pos k)))
      _ = ((2 * Real.pi) ^ 2 * wt k) ^ l.length * ((2 * Real.pi) ^ 2 * wt k) := by ring

lemma norm_dmulV_le (l : List ι) (c : (ι → ℤ) → ℂ) (k : ι → ℤ) :
    ‖dmulV l c k‖ ≤ (2 * Real.pi * wt k) ^ l.length * ‖c k‖ := by
  rw [dmulV, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_prod_dmulV_le l k) (norm_nonneg _)

lemma norm_sq_dmulV_le (l : List ι) (c : (ι → ℤ) → ℂ) (k : ι → ℤ) :
    ‖dmulV l c k‖ ^ 2 ≤ ((2 * Real.pi) ^ 2 * wt k) ^ l.length * ‖c k‖ ^ 2 := by
  rw [dmulV, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (norm_sq_prod_dmulV_le l k) (sq_nonneg _)

/-! ## The multiplier preserves the decay class -/

/-- The weighted `ℓ¹`-norms of `dmulV l c` are finite as soon as those of `c` are. -/
lemma summable_dmulV (l : List ι) (c : (ι → ℤ) → ℂ)
    (h : ∀ N : ℕ, Summable (fun k : ι → ℤ => (wt k) ^ N * ‖c k‖)) (N : ℕ) :
    Summable (fun k : ι → ℤ => (wt k) ^ N * ‖dmulV l c k‖) := by
  have hdom : Summable (fun k : ι → ℤ =>
      (2 * Real.pi) ^ l.length * ((wt k) ^ (N + l.length) * ‖c k‖)) :=
    (h (N + l.length)).mul_left _
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (wt_pos k).le N) (norm_nonneg _)) (fun k => ?_) hdom
  calc (wt k) ^ N * ‖dmulV l c k‖
      ≤ (wt k) ^ N * ((2 * Real.pi * wt k) ^ l.length * ‖c k‖) :=
        mul_le_mul_of_nonneg_left (norm_dmulV_le l c k) (pow_nonneg (wt_pos k).le N)
    _ = (2 * Real.pi) ^ l.length * ((wt k) ^ (N + l.length) * ‖c k‖) := by
        rw [mul_pow]; ring_nf

/-- The square of a nonnegative summable family is summable (the family is bounded by its sum). -/
lemma summable_sq_of_nonneg {α : Type*} {u : α → ℝ} (hu : Summable u) (h0 : ∀ a, 0 ≤ u a) :
    Summable (fun a => u a ^ 2) := by
  have hL : ∀ a, u a ≤ ∑' b, u b := fun a => hu.le_tsum a (fun b _ => h0 b)
  refine Summable.of_nonneg_of_le (fun a => sq_nonneg _) (fun a => ?_)
    (hu.mul_left (∑' b, u b))
  calc u a ^ 2 = u a * u a := by ring
    _ ≤ (∑' b, u b) * u a := mul_le_mul_of_nonneg_right (hL a) (h0 a)

/-- The weighted `ℓ¹`-decay hypothesis implies summability of the weighted `ℓ²`-summands of
`CSq`. -/
lemma summable_wt_pow_mul_norm_sq (c : (ι → ℤ) → ℂ)
    (h : ∀ N : ℕ, Summable (fun k : ι → ℤ => (wt k) ^ N * ‖c k‖)) (N : ℕ) :
    Summable (fun k : ι → ℤ => (wt k) ^ N * ‖c k‖ ^ 2) := by
  have h0 : Summable (fun k : ι → ℤ => ‖c k‖) := by simpa using h 0
  have hL : ∀ k : ι → ℤ, ‖c k‖ ≤ ∑' l : ι → ℤ, ‖c l‖ :=
    fun k => h0.le_tsum k (fun l _ => norm_nonneg _)
  have hdom : Summable (fun k : ι → ℤ =>
      (∑' l : ι → ℤ, ‖c l‖) * ((wt k) ^ N * ‖c k‖)) :=
    (h N).mul_left _
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (wt_pos k).le N) (sq_nonneg _)) (fun k => ?_) hdom
  calc (wt k) ^ N * ‖c k‖ ^ 2 = (wt k) ^ N * ‖c k‖ * ‖c k‖ := by ring
    _ ≤ (wt k) ^ N * ‖c k‖ * (∑' l : ι → ℤ, ‖c l‖) :=
        mul_le_mul_of_nonneg_left (hL k)
          (mul_nonneg (pow_nonneg (wt_pos k).le N) (norm_nonneg _))
    _ = (∑' l : ι → ℤ, ‖c l‖) * ((wt k) ^ N * ‖c k‖) := by ring

/-! ## The `L²` norm of a Fourier series -/

/-- **Parseval for a Fourier series.**  For `ℓ¹` coefficients the `L²` norm squared of the
series over the unit cube is the `ℓ²` norm squared of the coefficients. -/
lemma ens_integral_normSq_seriesFun (c : (ι → ℤ) → ℂ) (hc : Summable (fun k : ι → ℤ => ‖c k‖)) :
    (∫ x in unitCube, ‖seriesFun c x‖ ^ 2) = ∑' k : ι → ℤ, ‖c k‖ ^ 2 := by
  have hA := integral_seriesFun_mul_conj c c hc hc
  have hcongr : (∫ x in unitCube, seriesFun c x * star (seriesFun c x))
      = ∫ x in unitCube, ((‖seriesFun c x‖ ^ 2 : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h1 : (∫ x in unitCube, ((‖seriesFun c x‖ ^ 2 : ℝ) : ℂ))
      = ((∫ x in unitCube, ‖seriesFun c x‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
  have hB := hcongr.trans h1
  have hC : (∑' k : ι → ℤ, c k * star (c k))
      = ((∑' k : ι → ℤ, ‖c k‖ ^ 2 : ℝ) : ℂ) := by
    rw [show (fun k : ι → ℤ => c k * star (c k))
        = fun k => ((‖c k‖ ^ 2 : ℝ) : ℂ) from
      funext fun k => by rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]]
    exact (Complex.ofReal_tsum (fun k : ι → ℤ => ‖c k‖ ^ 2)).symm
  have : ((∫ x in unitCube, ‖seriesFun c x‖ ^ 2 : ℝ) : ℂ)
      = ((∑' k : ι → ℤ, ‖c k‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hB, hA, hC]
  exact Complex.ofReal_injective this

/-! ## Term by term differentiation of a Fourier series -/

/-- **Iterated term by term differentiation**: the derivative `pdList l` of a rapidly decaying
Fourier series is the Fourier series of the coefficient family `dmulV l c`. -/
lemma pdList_seriesFun (l : List ι) (c : (ι → ℤ) → ℂ)
    (h : ∀ N : ℕ, Summable (fun k : ι → ℤ => (wt k) ^ N * ‖c k‖)) :
    ∀ x : ι → ℝ, pdList l (seriesFun c) x = seriesFun (dmulV l c) x := by
  induction l with
  | nil => intro x; rw [dmulV_nil]; rfl
  | cons i l ih =>
    intro x
    have hfun : pdList l (seriesFun c) = seriesFun (dmulV l c) := funext ih
    rw [show pdList (i :: l) (seriesFun c) = pd i (pdList l (seriesFun c)) from rfl, hfun,
      pd_seriesFun i (dmulV l c) (summable_dmulV l c h), ← dmulV_cons i l c]

/-! ## The coefficient-side bound -/

/-- The weighted `ℓ²` energy of the differentiated coefficients is controlled by `CSq` at the
order of differentiation. -/
lemma tsum_normSq_dmulV_le (l : List ι) (c : (ι → ℤ) → ℂ)
    (h : ∀ N : ℕ, Summable (fun k : ι → ℤ => (wt k) ^ N * ‖c k‖)) :
    (∑' k : ι → ℤ, ‖dmulV l c k‖ ^ 2) ≤ ((2 * Real.pi) ^ 2) ^ l.length * CSq l.length c := by
  have hs : Summable (fun k : ι → ℤ => ‖dmulV l c k‖ ^ 2) :=
    summable_sq_of_nonneg (by simpa using summable_dmulV l c h 0) (fun k => norm_nonneg _)
  have hb : Summable (fun k : ι → ℤ =>
      ((2 * Real.pi) ^ 2) ^ l.length * ((wt k) ^ l.length * ‖c k‖ ^ 2)) :=
    (summable_wt_pow_mul_norm_sq c h l.length).mul_left _
  rw [CSq, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) hs hb
  calc ‖dmulV l c k‖ ^ 2 ≤ ((2 * Real.pi) ^ 2 * wt k) ^ l.length * ‖c k‖ ^ 2 :=
        norm_sq_dmulV_le l c k
    _ = ((2 * Real.pi) ^ 2) ^ l.length * ((wt k) ^ l.length * ‖c k‖ ^ 2) := by
        rw [mul_pow]; ring

/-! ## The target -/

theorem ENormSq_seriesFun_le {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : (ι → ℤ) → ℂ,
      (∀ N : ℕ, Summable (fun l : ι → ℤ => (Work.Diff.STE.wt l) ^ N * ‖c l‖)) →
      Work.Diff.STE.ENormSq k (Work.Diff.STE.seriesFun c) ≤ C * Work.Diff.STE.CSq k c := by
  refine ⟨(Fintype.card (Fin k → ι) : ℝ) * (2 * Real.pi) ^ (2 * k),
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _), fun c h => ?_⟩
  rw [ENormSq]
  calc ∑ l : Fin k → ι, ∫ x in unitCube, ‖pdVec k l (seriesFun c) x‖ ^ 2
      ≤ ∑ _l : Fin k → ι, (2 * Real.pi) ^ (2 * k) * CSq k c := by
        refine Finset.sum_le_sum (fun l _ => ?_)
        have hfun : pdVec k l (seriesFun c) = seriesFun (dmulV (List.ofFn l) c) :=
          funext (pdList_seriesFun (List.ofFn l) c h)
        rw [hfun,
          ens_integral_normSq_seriesFun (dmulV (List.ofFn l) c)
            (by simpa using summable_dmulV (List.ofFn l) c h 0)]
        calc ∑' k : ι → ℤ, ‖dmulV (List.ofFn l) c k‖ ^ 2
            ≤ ((2 * Real.pi) ^ 2) ^ (List.ofFn l).length * CSq (List.ofFn l).length c :=
              tsum_normSq_dmulV_le (List.ofFn l) c h
          _ = (2 * Real.pi) ^ (2 * k) * CSq k c := by rw [List.length_ofFn, pow_mul]
    _ = (Fintype.card (Fin k → ι) : ℝ) * ((2 * Real.pi) ^ (2 * k) * CSq k c) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ = (Fintype.card (Fin k → ι) : ℝ) * (2 * Real.pi) ^ (2 * k) * CSq k c := by ring

end Work.Diff.STE
