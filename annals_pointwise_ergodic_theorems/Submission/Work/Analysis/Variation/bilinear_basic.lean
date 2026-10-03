/-
# Bilinear arithmetic and `L^q` glue for the bilinear Rademacher--Menshov corollary

This module collects the elementary ingredients of the proof of the paper's Corollary `rm-bil`
(`Work.Analysis.Variation.rademacher_menshov_bilinear`):

* the pointwise consequences of the bilinearity of a map `B : V → W → X → ℂ` (vanishing on `0`,
  additivity and `ℂ`-homogeneity for finite sums, and the expansion of the mixed second difference
  `blockDelta2` of `(k₁, k₂) ↦ B (f k₁) (g k₂) x`);
* a.e.-measurability of `B` applied to finite linear combinations of a.e.-measurable families;
* the index conversion between sums over `(range n₁).product (range n₂)` and double sums over
  `Fin n₁ × Fin n₂`;
* a uniform (in `H`, `n`) Khintchine lower bound, for every exponent `q > 0`, obtained by gluing
  `Commons.Analysis.Walsh.exists_khintchine_hilbert` (for `q ≥ 1`) and
  `Work.Analysis.Variation.khintchine_lower_hilbert_small` (for `0 < q ≤ 1`);
* bridges between real norms and `ℝ≥0∞`-norms (`‖z‖ₑ = ofReal ‖z‖` for `z : ℂ`), and two
  elementary `eLpNorm` lemmas for `ℝ≥0∞`-valued functions (monotonicity, and homogeneity under
  multiplication by a constant).
-/
import Mathlib
import Submission.Work.Analysis.Variation.Defs
import Submission.Work.Analysis.Variation.khintchine_lower_hilbert_small
import Submission.Commons.Analysis.Walsh.exists_khintchine_hilbert
import Submission.Work.Analysis.Variation.finite_paley_zygmund_rpow
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal
open Finset MeasureTheory

namespace Work.Analysis.Variation

/-! ## 1. Bilinear arithmetic -/

section Bilinear

variable {V W X : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- `B 0 w = 0` for a map which is `ℂ`-homogeneous in its first argument. -/
lemma bil_zero₁ (B : V → W → X → ℂ)
    (hsmul₁ : ∀ (c : ℂ) (v : V) (w : W), B (c • v) w = c • B v w) (w : W) :
    (fun x => B 0 w x) = 0 := by
  have h := hsmul₁ 0 (0 : V) w
  simpa using h

/-- `B v 0 = 0` for a map which is `ℂ`-homogeneous in its second argument. -/
lemma bil_zero₂ (B : V → W → X → ℂ)
    (hsmul₂ : ∀ (c : ℂ) (v : V) (w : W), B v (c • w) = c • B v w) (v : V) :
    (fun x => B v 0 x) = 0 := by
  have h := hsmul₂ 0 v (0 : W)
  simpa using h

/-- Additivity in the first argument, evaluated at `x`. -/
lemma bil_add₁_apply (B : V → W → X → ℂ)
    (hadd₁ : ∀ (v v' : V) (w : W), B (v + v') w = B v w + B v' w)
    (v v' : V) (w : W) (x : X) : B (v + v') w x = B v w x + B v' w x := by
  have h := congrFun (hadd₁ v v' w) x
  simpa using h

/-- Additivity in the second argument, evaluated at `x`. -/
lemma bil_add₂_apply (B : V → W → X → ℂ)
    (hadd₂ : ∀ (v : V) (w w' : W), B v (w + w') = B v w + B v w')
    (v : V) (w w' : W) (x : X) : B v (w + w') x = B v w x + B v w' x := by
  have h := congrFun (hadd₂ v w w') x
  simpa using h

/-- `ℂ`-homogeneity in the first argument, evaluated at `x`. -/
lemma bil_smul₁_apply (B : V → W → X → ℂ)
    (hsmul₁ : ∀ (c : ℂ) (v : V) (w : W), B (c • v) w = c • B v w)
    (c : ℂ) (v : V) (w : W) (x : X) : B (c • v) w x = c * B v w x := by
  have h := congrFun (hsmul₁ c v w) x
  simpa using h

/-- `ℂ`-homogeneity in the second argument, evaluated at `x`. -/
lemma bil_smul₂_apply (B : V → W → X → ℂ)
    (hsmul₂ : ∀ (c : ℂ) (v : V) (w : W), B v (c • w) = c • B v w)
    (c : ℂ) (v : V) (w : W) (x : X) : B v (c • w) x = c * B v w x := by
  have h := congrFun (hsmul₂ c v w) x
  simpa using h

/-- Additivity for differences in the first argument, evaluated at `x`. -/
lemma bil_sub₁_apply (B : V → W → X → ℂ)
    (hadd₁ : ∀ (v v' : V) (w : W), B (v + v') w = B v w + B v' w)
    (hsmul₁ : ∀ (c : ℂ) (v : V) (w : W), B (c • v) w = c • B v w)
    (v v' : V) (w : W) (x : X) : B (v - v') w x = B v w x - B v' w x := by
  have hneg : (-v' : V) = (-1 : ℂ) • v' := (neg_one_smul ℂ v').symm
  calc B (v - v') w x = B (v + (-v')) w x := by rw [sub_eq_add_neg]
    _ = B v w x + B (-v') w x := bil_add₁_apply B hadd₁ v (-v') w x
    _ = B v w x + (-1 : ℂ) * B v' w x := by rw [hneg, bil_smul₁_apply B hsmul₁]
    _ = B v w x - B v' w x := by ring

/-- Additivity for differences in the second argument, evaluated at `x`. -/
lemma bil_sub₂_apply (B : V → W → X → ℂ)
    (hadd₂ : ∀ (v : V) (w w' : W), B v (w + w') = B v w + B v w')
    (hsmul₂ : ∀ (c : ℂ) (v : V) (w : W), B v (c • w) = c • B v w)
    (v : V) (w w' : W) (x : X) : B v (w - w') x = B v w x - B v w' x := by
  have hneg : (-w' : W) = (-1 : ℂ) • w' := (neg_one_smul ℂ w').symm
  calc B v (w - w') x = B v (w + (-w')) x := by rw [sub_eq_add_neg]
    _ = B v w x + B v (-w') x := bil_add₂_apply B hadd₂ v w (-w') x
    _ = B v w x + (-1 : ℂ) * B v w' x := by rw [hneg, bil_smul₂_apply B hsmul₂]
    _ = B v w x - B v w' x := by ring

/-- Linearity in the first argument for a finite linear combination. -/
lemma bil_sum₁_apply (B : V → W → X → ℂ)
    (hadd₁ : ∀ (v v' : V) (w : W), B (v + v') w = B v w + B v' w)
    (hsmul₁ : ∀ (c : ℂ) (v : V) (w : W), B (c • v) w = c • B v w)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (v : ι → V) (w : W) (x : X) :
    B (∑ i ∈ s, c i • v i) w x = ∑ i ∈ s, c i * B (v i) w x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using congrFun (bil_zero₁ B hsmul₁ w) x
  | insert a s ha ih =>
      have hsum : (∑ i ∈ insert a s, c i • v i) = c a • v a + ∑ i ∈ s, c i • v i :=
        Finset.sum_insert ha
      rw [hsum, bil_add₁_apply B hadd₁, bil_smul₁_apply B hsmul₁, ih, Finset.sum_insert ha]

/-- Linearity in the second argument for a finite linear combination. -/
lemma bil_sum₂_apply (B : V → W → X → ℂ)
    (hadd₂ : ∀ (v : V) (w w' : W), B v (w + w') = B v w + B v w')
    (hsmul₂ : ∀ (c : ℂ) (v : V) (w : W), B v (c • w) = c • B v w)
    {κ : Type*} (t : Finset κ) (d : κ → ℂ) (w : κ → W) (v : V) (x : X) :
    B v (∑ j ∈ t, d j • w j) x = ∑ j ∈ t, d j * B v (w j) x := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using congrFun (bil_zero₂ B hsmul₂ v) x
  | insert a t ha ih =>
      have hsum : (∑ j ∈ insert a t, d j • w j) = d a • w a + ∑ j ∈ t, d j • w j :=
        Finset.sum_insert ha
      rw [hsum, bil_add₂_apply B hadd₂, bil_smul₂_apply B hsmul₂, ih, Finset.sum_insert ha]

/-- Bilinearity for a pair of finite linear combinations. -/
lemma bil_sum_sum_apply (B : V → W → X → ℂ)
    (hadd₁ : ∀ (v v' : V) (w : W), B (v + v') w = B v w + B v' w)
    (hsmul₁ : ∀ (c : ℂ) (v : V) (w : W), B (c • v) w = c • B v w)
    (hadd₂ : ∀ (v : V) (w w' : W), B v (w + w') = B v w + B v w')
    (hsmul₂ : ∀ (c : ℂ) (v : V) (w : W), B v (c • w) = c • B v w)
    {ι κ : Type*} (s : Finset ι) (t : Finset κ) (c : ι → ℂ) (d : κ → ℂ)
    (v : ι → V) (w : κ → W) (x : X) :
    B (∑ i ∈ s, c i • v i) (∑ j ∈ t, d j • w j) x
      = ∑ i ∈ s, ∑ j ∈ t, (c i * d j) * B (v i) (w j) x := by
  rw [bil_sum₁_apply B hadd₁ hsmul₁]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bil_sum₂_apply B hadd₂ hsmul₂, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Bilinearity for a pair of finite linear combinations, indexed by `Fin`. -/
lemma bil_sum_sum_fin_apply (B : V → W → X → ℂ)
    (hadd₁ : ∀ (v v' : V) (w : W), B (v + v') w = B v w + B v' w)
    (hsmul₁ : ∀ (c : ℂ) (v : V) (w : W), B (c • v) w = c • B v w)
    (hadd₂ : ∀ (v : V) (w w' : W), B v (w + w') = B v w + B v w')
    (hsmul₂ : ∀ (c : ℂ) (v : V) (w : W), B v (c • w) = c • B v w)
    {n₁ n₂ : ℕ} (d₁ : Fin n₁ → Bool) (d₂ : Fin n₂ → Bool) (v : ℕ → V) (w : ℕ → W) (x : X) :
    B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ)) (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x
      = ∑ i : Fin n₁, ∑ j : Fin n₂,
          (sgn (d₁ i) * sgn (d₂ j)) * B (v (i : ℕ)) (w (j : ℕ)) x := by
  rw [bil_sum_sum_apply B hadd₁ hsmul₁ hadd₂ hsmul₂ Finset.univ Finset.univ
    (fun i : Fin n₁ => sgn (d₁ i)) (fun j : Fin n₂ => sgn (d₂ j))
    (fun i : Fin n₁ => v (i : ℕ)) (fun j : Fin n₂ => w (j : ℕ)) x]

/-- The mixed second difference of `(k₁, k₂) ↦ B (f k₁) (g k₂) x` over the rectangle of side
lengths `M₁, M₂` with lower-left corner `(L₁, L₂)` and right ends truncated at `K` is the value
of `B` on the corresponding increments of `f` and of `g`. -/
lemma blockDelta2_eq_apply (B : V → W → X → ℂ)
    (hadd₁ : ∀ (v v' : V) (w : W), B (v + v') w = B v w + B v' w)
    (hsmul₁ : ∀ (c : ℂ) (v : V) (w : W), B (c • v) w = c • B v w)
    (hadd₂ : ∀ (v : V) (w w' : W), B v (w + w') = B v w + B v w')
    (hsmul₂ : ∀ (c : ℂ) (v : V) (w : W), B v (c • w) = c • B v w)
    (f : ℕ → V) (g : ℕ → W) (K M₁ L₁ M₂ L₂ : ℕ) (x : X) :
    blockDelta2 (fun k₁ k₂ => B (f k₁) (g k₂) x) K M₁ L₁ M₂ L₂
      = B (f (min (L₁ + M₁) K) - f L₁) (g (min (L₂ + M₂) K) - g L₂) x := by
  dsimp only [blockDelta2]
  rw [bil_sub₁_apply B hadd₁ hsmul₁, bil_sub₂_apply B hadd₂ hsmul₂,
    bil_sub₂_apply B hadd₂ hsmul₂]
  ring

end Bilinear

/-! ## 2. Index conversions -/

/-- A sum over the product of two `range`s is a double sum over `Fin`. -/
lemma sum_product_range_eq_sum_fin {M : Type*} [AddCommMonoid M] (n₁ n₂ : ℕ)
    (g : ℕ → ℕ → M) :
    (∑ p ∈ (Finset.range n₁).product (Finset.range n₂), g p.1 p.2)
      = ∑ i : Fin n₁, ∑ j : Fin n₂, g (i : ℕ) (j : ℕ) := by
  change (∑ p ∈ Finset.range n₁ ×ˢ Finset.range n₂, g p.1 p.2) = _
  rw [Finset.sum_product (Finset.range n₁) (Finset.range n₂) (fun p => g p.1 p.2)]
  conv_rhs => rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin n₂, g i (j : ℕ)) n₁]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Fin.sum_univ_eq_sum_range (fun j => g i j) n₂]

/-! ## 3. A.e.-measurability of `B` on finite linear combinations -/

section Measurable

variable {V W X : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [MeasurableSpace X] {μ : Measure X}

/-- If all the values `B (v i) (w j) ·` are a.e.-measurable, then so is `B` applied to finite
linear combinations of the `v i` and of the `w j`. -/
lemma aemeasurable_bilinear_sum (B : V → W → X → ℂ)
    (hadd₁ : ∀ (v v' : V) (w : W), B (v + v') w = B v w + B v' w)
    (hsmul₁ : ∀ (c : ℂ) (v : V) (w : W), B (c • v) w = c • B v w)
    (hadd₂ : ∀ (v : V) (w w' : W), B v (w + w') = B v w + B v w')
    (hsmul₂ : ∀ (c : ℂ) (v : V) (w : W), B v (c • w) = c • B v w)
    {ι κ : Type*} (v : ι → V) (w : κ → W) (s : Finset ι) (t : Finset κ)
    (c : ι → ℂ) (d : κ → ℂ)
    (hmeas : ∀ (i : ι) (j : κ), _root_.AEMeasurable (fun x => B (v i) (w j) x) μ) :
    _root_.AEMeasurable (fun x => B (∑ i ∈ s, c i • v i) (∑ j ∈ t, d j • w j) x) μ := by
  rw [show (fun x => B (∑ i ∈ s, c i • v i) (∑ j ∈ t, d j • w j) x)
        = fun x => ∑ i ∈ s, ∑ j ∈ t, (c i * d j) * B (v i) (w j) x from
      funext fun x => bil_sum_sum_apply B hadd₁ hsmul₁ hadd₂ hsmul₂ s t c d v w x]
  exact Finset.aemeasurable_fun_sum s fun i _ =>
    Finset.aemeasurable_fun_sum t fun j _ => (hmeas i j).const_mul (c i * d j)

/-- Fin-indexed form of `aemeasurable_bilinear_sum`: a.e.-measurability of `B` applied to two
Rademacher sums of a.e.-measurable families. -/
lemma aemeasurable_bilinear_fin (B : V → W → X → ℂ)
    (hadd₁ : ∀ (v v' : V) (w : W), B (v + v') w = B v w + B v' w)
    (hsmul₁ : ∀ (c : ℂ) (v : V) (w : W), B (c • v) w = c • B v w)
    (hadd₂ : ∀ (v : V) (w w' : W), B v (w + w') = B v w + B v w')
    (hsmul₂ : ∀ (c : ℂ) (v : V) (w : W), B v (c • w) = c • B v w)
    (v : ℕ → V) (w : ℕ → W) {n₁ n₂ : ℕ} (d₁ : Fin n₁ → Bool) (d₂ : Fin n₂ → Bool)
    (hmeas : ∀ (i j : ℕ), _root_.AEMeasurable (fun x => B (v i) (w j) x) μ) :
    _root_.AEMeasurable (fun x => B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
      (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x) μ := by
  rw [show (fun x => B (∑ i : Fin n₁, sgn (d₁ i) • v (i : ℕ))
        (∑ j : Fin n₂, sgn (d₂ j) • w (j : ℕ)) x)
      = fun x => ∑ i : Fin n₁, ∑ j : Fin n₂,
          (sgn (d₁ i) * sgn (d₂ j)) * B (v (i : ℕ)) (w (j : ℕ)) x from
    funext fun x => bil_sum_sum_fin_apply B hadd₁ hsmul₁ hadd₂ hsmul₂ d₁ d₂ v w x]
  exact Finset.aemeasurable_fun_sum Finset.univ fun i _ =>
    Finset.aemeasurable_fun_sum Finset.univ fun j _ => (hmeas (i : ℕ) (j : ℕ)).const_mul _

end Measurable

/-! ## 4. A uniform Khintchine lower bound for all exponents `q > 0` -/

universe u

/-- The real sign `±1` coerced to `ℂ` is the complex sign `±1`. -/
lemma rmb_sign_cast (b : Bool) :
    ((if b then (1 : ℝ) else -1) : ℂ) = (if b then (1 : ℂ) else -1) := by
  cases b <;> norm_num

/-- **Khintchine's inequality (lower half) for `0 < q ≤ 1`, uniformly in the Hilbert space and in
`n`.**  There is `c = c q > 0` such that for every complex Hilbert space `H`, every `n` and every
`x : Fin n → H`, `c (∑ᵢ ‖xᵢ‖²)^{1/2} ≤ (2^{-n} ∑_{ε} ‖∑ᵢ εᵢ xᵢ‖^q)^{1/q}`.

This is the Paley--Zygmund argument of
`Work.Analysis.Variation.khintchine_lower_hilbert_small`, run once with the constant of
`Commons.Analysis.Walsh.rademacher_hilbert_even_moment` (which is uniform in `H` and `n`) and the
Paley--Zygmund lemma `Work.Analysis.Variation.finite_paley_zygmund_rpow`; the only difference from
the source is that `H` is quantified *inside* the `∃ c`, which is what the bilinear corollary
needs. -/
theorem khintchine_lower_hilbert_small_uniform {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (n : ℕ) (x : Fin n → H),
        c * (∑ i : Fin n, ‖x i‖ ^ 2) ^ ((1 : ℝ) / 2)
          ≤ ((∑ e : Fin n → Bool,
              ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖ ^ q) / (2 : ℝ) ^ n)
            ^ ((1 : ℝ) / q) := by
  classical
  obtain ⟨K, _hKpos, hKeven⟩ := Commons.Analysis.Walsh.rademacher_hilbert_even_moment
  refine ⟨(4 * (K * 2) ^ 2) ^ (-(1 / q)) / Real.sqrt 2, ?_, ?_⟩
  · exact div_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.sqrt_pos.mpr (by norm_num))
  · intro H _ _ n x
    have hcard : ((Fintype.card (Fin n → Bool) : ℕ) : ℝ) = (2 : ℝ) ^ n := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]; push_cast; ring
    have hι : 0 < Fintype.card (Fin n → Bool) := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]; norm_num
    set W : (Fin n → Bool) → ℝ :=
      fun e => ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖ with hWdef
    set σ : ℝ := ∑ i : Fin n, ‖x i‖ ^ (2 : ℕ) with hσdef
    have h2 : ∑ e, W e ^ (2 : ℕ) = (Fintype.card (Fin n → Bool) : ℝ) * σ := by
      rw [hWdef, hσdef, hcard]
      rw [← Commons.Analysis.Walsh.rademacher_parseval_inner n x]
      exact Finset.sum_congr rfl fun e _ => by simp only [rmb_sign_cast]
    have h4 : ∑ e, W e ^ (4 : ℕ) ≤ (K * 2) ^ 2 * (Fintype.card (Fin n → Bool) : ℝ) * σ ^ (2 : ℕ) := by
      have h := hKeven 2 (by norm_num) (H := H) n x
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)] at h
      rw [← hcard, ← hσdef] at h
      have hh : (∑ e : Fin n → Bool, W e ^ (4 : ℕ))
          ≤ (K * 2) ^ 2 * σ ^ (2 : ℕ) * (Fintype.card (Fin n → Bool) : ℝ) := h
      calc (∑ e : Fin n → Bool, W e ^ (4 : ℕ))
          ≤ (K * 2) ^ 2 * σ ^ (2 : ℕ) * (Fintype.card (Fin n → Bool) : ℝ) := hh
        _ = (K * 2) ^ 2 * (Fintype.card (Fin n → Bool) : ℝ) * σ ^ (2 : ℕ) := by ring
    have hPZ := finite_paley_zygmund_rpow (ι := Fin n → Bool) hι W (fun e => norm_nonneg _)
        (σ2 := σ) (C := (K * 2) ^ 2) (by positivity) (by positivity) h2 h4 hq
    rw [← hcard]
    exact hPZ

/-- **Khintchine's inequality (lower half), uniformly for every exponent `q > 0`.**  There is
`c = c q > 0` such that for every complex Hilbert space `H`, every `n` and every `x : Fin n → H`,
`c (∑ᵢ ‖xᵢ‖²)^{1/2} ≤ (2^{-n} ∑_{ε} ‖∑ᵢ εᵢ xᵢ‖^q)^{1/q}`.

For `q ≥ 1` this is the lower half of `Commons.Analysis.Walsh.exists_khintchine_hilbert` (whose
constant is uniform in `H` and `n`); for `0 < q ≤ 1` it is
`khintchine_lower_hilbert_small_uniform` above. -/
theorem khintchine_lower_all_q (q : ℝ) (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (n : ℕ) (x : Fin n → H),
        c * (∑ i : Fin n, ‖x i‖ ^ 2) ^ ((1 : ℝ) / 2)
          ≤ ((∑ e : Fin n → Bool,
              ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖ ^ q) / (2 : ℝ) ^ n)
            ^ ((1 : ℝ) / q) := by
  rcases le_or_gt q 1 with hq1 | hq1
  · obtain ⟨c, hc, h⟩ := khintchine_lower_hilbert_small_uniform.{u} hq hq1
    exact ⟨c, hc, fun {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (n : ℕ)
      (x : Fin n → H) => h n x⟩
  · obtain ⟨c, _C, hc, _hC, h⟩ := Commons.Analysis.Walsh.exists_khintchine_hilbert.{u} q hq1.le
    exact ⟨c, hc, fun {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (n : ℕ)
      (x : Fin n → H) => (h n x).1⟩

/-! ## 5. Real norms versus `ℝ≥0∞`-norms -/

/-- For a complex number, the `ℝ≥0∞`-norm is the `ofReal` of the norm. -/
lemma enorm_complex_eq_ofReal (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]
  rfl

/-- Powers of the `ℝ≥0∞`-norm of a complex number, in terms of `ofReal`. -/
lemma enorm_complex_rpow_eq_ofReal (z : ℂ) {q : ℝ} (hq : 0 ≤ q) :
    ‖z‖ₑ ^ q = ENNReal.ofReal (‖z‖ ^ q) := by
  rw [enorm_complex_eq_ofReal, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg z) hq]

/-! ## 6. `eLpNorm` glue for `ℝ≥0∞`-valued functions -/

section LpGlue

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Monotonicity of `eLpNorm` on `ℝ≥0∞`-valued functions. -/
lemma eLpNorm_le_of_le {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpT : p ≠ ⊤) {F G : X → ℝ≥0∞}
    (h : ∀ x, F x ≤ G x) (hF : AEStronglyMeasurable F μ := by pw_aesm) :
    eLpNorm F p μ ≤ eLpNorm G p μ := by
  by_cases hG : AEStronglyMeasurable G μ
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hG]; exact le_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpT hF,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpT hG]
  simp only [enorm_eq_self]
  refine ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_)
    (div_nonneg zero_le_one ENNReal.toReal_nonneg)
  exact ENNReal.rpow_le_rpow (h x) ENNReal.toReal_nonneg

/-- Homogeneity of `eLpNorm` on `ℝ≥0∞`-valued functions under multiplication by a constant. -/
lemma eLpNorm_const_mul_ennreal {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpT : p ≠ ⊤) (c : ℝ≥0∞)
    {F : X → ℝ≥0∞} (hF : _root_.AEMeasurable F μ) :
    eLpNorm (fun x => c * F x) p μ = c * eLpNorm F p μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpT,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpT]
  simp only [enorm_eq_self]
  have hq0 : (0 : ℝ) < p.toReal := ENNReal.toReal_pos hp0 hpT
  have hpow : (fun x => (c * F x) ^ p.toReal)
      = fun x => c ^ p.toReal * F x ^ p.toReal := by
    funext x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hq0)]
  rw [hpow, lintegral_const_mul'' _ (hF.pow_const _)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  congr 1
  rw [← ENNReal.rpow_mul, show p.toReal * (1 / p.toReal) = 1 by
    rw [mul_one_div, div_self hq0.ne'], ENNReal.rpow_one]

end LpGlue

end Work.Analysis.Variation
