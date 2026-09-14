import Mathlib
import Submission.Commons.MeasureTheory.Integral.lintegral_ofReal_sq_deriv_le_liminf
import Submission.Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_deriv_integral_vector
import Submission.Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_ae_differentiableAt_vector

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Commons.MeasureTheory.Integral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

/-! ### The mass scaling as a continuous linear map

For masses `m : Fin N → ℝ` we consider the continuous linear map `v ↦ (√(mᵢ/2) • vᵢ)ᵢ` on
`EuclideanSpace E (Fin N)`.  Its defining property is `‖A v‖ ^ 2 = 1/2 * ∑ i, mᵢ ‖vᵢ‖ ^ 2`, so
that the Dirichlet energy `∫⁻ ofReal ‖(A ∘ f)'‖²` of a mass-scaled curve is exactly
`∫⁻ ofReal (1/2 * ∑ i, mᵢ ‖fᵢ'‖²)`, the mass-weighted kinetic energy of `f`. -/

private noncomputable def massScaleLinear (m : Fin N → ℝ) : (Fin N → E) →L[ℝ] (Fin N → E) :=
  ContinuousLinearMap.pi (fun i : Fin N =>
    (Real.sqrt (m i / 2)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => E) i)

private noncomputable def toPiCLM : EuclideanSpace E (Fin N) →L[ℝ] (Fin N → E) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => E)

private noncomputable def ofPiCLM : (Fin N → E) →L[ℝ] EuclideanSpace E (Fin N) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => E)).symm

/-- The mass scaling of a configuration, as a continuous linear map: `v ↦ (√(mᵢ/2) • vᵢ)ᵢ` on
`EuclideanSpace E (Fin N)`.  The factor `1/2` is built in so that `‖A v‖ ^ 2` is precisely
`1/2 * ∑ i, mᵢ ‖vᵢ‖ ^ 2`, the mass-weighted kinetic energy. -/
noncomputable def massScaleCLM (m : Fin N → ℝ) :
    EuclideanSpace E (Fin N) →L[ℝ] EuclideanSpace E (Fin N) :=
  (ofPiCLM (E := E)).comp ((massScaleLinear m).comp (toPiCLM (E := E) (N := N)))

@[simp]
lemma massScaleCLM_apply (m : Fin N → ℝ) (v : EuclideanSpace E (Fin N)) (i : Fin N) :
    massScaleCLM m v i = Real.sqrt (m i / 2) • v i := rfl

lemma massScaleCLM_ofLp (m : Fin N → ℝ) (v : EuclideanSpace E (Fin N)) (i : Fin N) :
    (massScaleCLM m v).ofLp i = Real.sqrt (m i / 2) • v i := rfl

/-- The defining property of the mass scaling: squared norms are the mass-weighted energies. -/
lemma massScaleCLM_norm_sq (m : Fin N → ℝ) (hm : ∀ i, 0 ≤ m i)
    (v : EuclideanSpace E (Fin N)) :
    ‖massScaleCLM m v‖ ^ 2 = (1 / 2) * ∑ i, m i * ‖v i‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [massScaleCLM_ofLp, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (div_nonneg (hm i) (by norm_num))]
  ring

/-- Upper bound: the mass scaling is Lipschitz with constant `√(1/2 * ∑ᵢ mᵢ)`. -/
lemma massScaleCLM_norm_le (m : Fin N → ℝ) (hm : ∀ i, 0 ≤ m i)
    (v : EuclideanSpace E (Fin N)) :
    ‖massScaleCLM m v‖ ≤ Real.sqrt ((1 / 2) * ∑ i, m i) * ‖v‖ := by
  have hsum : ∑ i, m i * ‖v i‖ ^ 2 ≤ ∑ i, m i * ‖v‖ ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le v i) 2) (hm i)
  have hsum2 : ∑ i, m i * ‖v‖ ^ 2 = (∑ i, m i) * ‖v‖ ^ 2 :=
    (Finset.sum_mul Finset.univ (fun i => m i) (‖v‖ ^ 2)).symm
  have hkey : ‖massScaleCLM m v‖ ^ 2 ≤ ((1 / 2) * ∑ i, m i) * ‖v‖ ^ 2 := by
    rw [massScaleCLM_norm_sq m hm v]
    calc (1 / 2) * ∑ i, m i * ‖v i‖ ^ 2
        ≤ (1 / 2) * ∑ i, m i * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = (1 / 2) * ((∑ i, m i) * ‖v‖ ^ 2) := by rw [hsum2]
      _ = ((1 / 2) * ∑ i, m i) * ‖v‖ ^ 2 := by ring
  calc ‖massScaleCLM m v‖
      = Real.sqrt (‖massScaleCLM m v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (((1 / 2) * ∑ i, m i) * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hkey
    _ = Real.sqrt ((1 / 2) * ∑ i, m i) * ‖v‖ := by
        rw [Real.sqrt_mul (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => hm i)),
          Real.sqrt_sq (norm_nonneg _)]

/-- Lower bound: if `0 < c ≤ mᵢ` then `√(c/2) ‖v‖ ≤ ‖A v‖`, i.e. the mass scaling is
non-degenerate. -/
lemma sqrt_half_mul_norm_le_massScaleCLM (m : Fin N → ℝ) {c : ℝ} (hc : 0 < c)
    (hm : ∀ i, c ≤ m i) (v : EuclideanSpace E (Fin N)) :
    Real.sqrt ((1 / 2) * c) * ‖v‖ ≤ ‖massScaleCLM m v‖ := by
  have hsq : ‖v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin N => E) v
  have hsum3 : ∑ i, c * ‖v i‖ ^ 2 = c * ‖v‖ ^ 2 := by
    rw [hsq, Finset.mul_sum]
  have hle : ∑ i, c * ‖v i‖ ^ 2 ≤ ∑ i, m i * ‖v i‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hm i) (by positivity)
  have hkey : ((1 / 2) * c) * ‖v‖ ^ 2 ≤ ‖massScaleCLM m v‖ ^ 2 := by
    rw [massScaleCLM_norm_sq m (fun i => le_trans hc.le (hm i)) v]
    calc ((1 / 2) * c) * ‖v‖ ^ 2
        = (1 / 2) * (c * ‖v‖ ^ 2) := by ring
      _ = (1 / 2) * ∑ i, c * ‖v i‖ ^ 2 := by rw [hsum3]
      _ ≤ (1 / 2) * ∑ i, m i * ‖v i‖ ^ 2 := mul_le_mul_of_nonneg_left hle (by norm_num)
  calc Real.sqrt ((1 / 2) * c) * ‖v‖
      = Real.sqrt (((1 / 2) * c) * ‖v‖ ^ 2) := by
        rw [Real.sqrt_mul (by linarith : (0:ℝ) ≤ (1 / 2) * c), Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (‖massScaleCLM m v‖ ^ 2) := Real.sqrt_le_sqrt hkey
    _ = ‖massScaleCLM m v‖ := Real.sqrt_sq (norm_nonneg _)

/-- The distance form of the upper bound. -/
lemma massScaleCLM_dist_le (m : Fin N → ℝ) (hm : ∀ i, 0 ≤ m i)
    (x y : EuclideanSpace E (Fin N)) :
    dist (massScaleCLM m x) (massScaleCLM m y)
      ≤ Real.sqrt ((1 / 2) * ∑ i, m i) * dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact massScaleCLM_norm_le m hm (x - y)

/-- The distance form of the lower bound. -/
lemma massScaleCLM_dist_ge (m : Fin N → ℝ) {c : ℝ} (hc : 0 < c) (hm : ∀ i, c ≤ m i)
    (x y : EuclideanSpace E (Fin N)) :
    dist x y ≤ (Real.sqrt ((1 / 2) * c))⁻¹ * dist (massScaleCLM m x) (massScaleCLM m y) := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  have h := sqrt_half_mul_norm_le_massScaleCLM m hc hm (x - y)
  have hpos : 0 < Real.sqrt ((1 / 2) * c) := Real.sqrt_pos.mpr (by linarith)
  calc ‖x - y‖ = (Real.sqrt ((1 / 2) * c))⁻¹ * (Real.sqrt ((1 / 2) * c) * ‖x - y‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
    _ ≤ (Real.sqrt ((1 / 2) * c))⁻¹ * ‖massScaleCLM m (x - y)‖ :=
        mul_le_mul_of_nonneg_left h (by positivity)

/-! ### Two elementary composition lemmas -/

/-- Uniform convergence is preserved by postcomposition with a Lipschitz map. -/
theorem tendstoUniformlyOn_comp_dist_le {α β γ : Type*} [PseudoMetricSpace β]
    [PseudoMetricSpace γ] {F : ℕ → α → β} {f : α → β} {L : β → γ} {s : Set α} {K : ℝ}
    (hK : 0 ≤ K) (hL : ∀ x y, dist (L x) (L y) ≤ K * dist x y)
    (h : TendstoUniformlyOn F f atTop s) :
    TendstoUniformlyOn (fun n => L ∘ F n) (L ∘ f) atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h (ε / (K + 1)) (by positivity)] with n hn x hx
  calc dist (L (f x)) (L (F n x)) ≤ K * dist (f x) (F n x) := hL _ _
    _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left (hn x hx).le hK
    _ < ε := by
        have h1 : K * (ε / (K + 1)) = (K * ε) / (K + 1) := by ring
        rw [h1, div_lt_iff₀ (by linarith : (0:ℝ) < K + 1)]
        nlinarith [hε]

/-- Absolute continuity survives composition with a map `L` whose *inverse* is Lipschitz. -/
theorem absolutelyContinuousOnInterval_of_comp_dist_le {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {L : X → Y} {a b : ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hL : ∀ x y, dist x y ≤ K * dist (L x) (L y)) (f : ℝ → X)
    (hf : AbsolutelyContinuousOnInterval (L ∘ f) a b) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := hf (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδpos, fun E hE hlt => ?_⟩
  calc ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)
      ≤ ∑ i ∈ Finset.range E.1, K * dist (L (f (E.2 i).1)) (L (f (E.2 i).2)) :=
        Finset.sum_le_sum fun i _ => hL _ _
    _ = K * ∑ i ∈ Finset.range E.1, dist (L (f (E.2 i).1)) (L (f (E.2 i).2)) := by
        rw [Finset.mul_sum]
    _ ≤ (K + 1) * ∑ i ∈ Finset.range E.1, dist (L (f (E.2 i).1)) (L (f (E.2 i).2)) := by
        have hnn : 0 ≤ ∑ i ∈ Finset.range E.1,
            dist (L (f (E.2 i).1)) (L (f (E.2 i).2)) :=
          Finset.sum_nonneg fun _ _ => dist_nonneg
        nlinarith
    _ < (K + 1) * (ε / (K + 1)) := mul_lt_mul_of_pos_left (hδ E hE hlt) (by linarith)
    _ = ε := by field_simp

/-- Almost everywhere, the derivative of `t ↦ A (u t)` is `A (deriv u t)`, for an absolutely
continuous `u`. -/
lemma ae_deriv_massScaleCLM {m : Fin N → ℝ} {u : ℝ → EuclideanSpace E (Fin N)} {τ : ℝ}
    (hτ : 0 ≤ τ) (hACu : AbsolutelyContinuousOnInterval u 0 τ) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc 0 τ →
      deriv (fun s => massScaleCLM m (u s)) t = massScaleCLM m (deriv u t) := by
  filter_upwards [absolutelyContinuousOnInterval_ae_differentiableAt_vector hACu] with t ht htIoc
  have htIcc : t ∈ Set.Icc 0 τ := ⟨le_of_lt htIoc.1, htIoc.2⟩
  have hdiff : DifferentiableAt ℝ u t := ht (by rw [uIcc_of_le hτ]; exact htIcc)
  have hd := ((massScaleCLM m).hasFDerivAt (x := u t)).comp_hasDerivAt t hdiff.hasDerivAt
  simpa [Function.comp_def] using hd.deriv

/-- **Lower semicontinuity of the mass-weighted Dirichlet energy under uniform convergence.**
Let `c > 0` with `c ≤ m i` for all `i` (so the mass scaling is non-degenerate), let `F n` be
absolutely continuous curves on `[0,τ]` converging uniformly on `[0,τ]` to a continuous `g`, and
suppose the energies `∫⁻ ½∑ᵢ mᵢ ‖(F n)'ᵢ‖²` are uniformly bounded by `ofReal (M^2)`
(this uniform bound is necessary: without it the statement is false -- the Cantor staircase is a
uniform limit of piecewise linear curves with divergent energies, and is not absolutely
continuous).  Then `g` is absolutely continuous and
`∫⁻_{Ioc 0 τ} ½∑ᵢ mᵢ ‖g'ᵢ‖² ≤ liminf_n ∫⁻_{Ioc 0 τ} ½∑ᵢ mᵢ ‖(F n)'ᵢ‖²`.

Suggested route: reduce to
`Commons.MeasureTheory.Integral.lintegral_ofReal_sq_deriv_le_liminf` applied to the mass-scaled
curves `A ∘ F n` and `A ∘ g`, where `A v = (√(mᵢ) • vᵢ)ᵢ` on `EuclideanSpace E (Fin N)`; `A` is an
injective continuous linear map (build it as a `LinearMap` from the coordinatewise description with
`LinearMap.mkContinuous`, using `‖A v‖² = ∑ᵢ mᵢ ‖vᵢ‖²` — this is `PiLp.norm_sq_eq_of_L2` plus
`Real.sq_sqrt`, and gives the norm bound `‖A v‖ ≤ √(∑ᵢ mᵢ) ‖v‖`).  Composition with a continuous
linear map preserves absolute continuity
(`Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_of_dist_le`) and its
derivative is `A (deriv g t)` (`ContinuousLinearMap.hasFDerivAt` composed with `HasDerivAt`).
Finally use `ENNReal.ofReal_mul` to write `ofReal (½ ∑ᵢ mᵢ ‖vᵢ‖²) = ofReal (1/2) * ofReal (‖A v‖²)`
and the monotonicity `ofReal (1/2) * liminf_n b n ≤ liminf_n (ofReal (1/2) * b n)`
(`mul_iSup_of_ne`/`mul_iInf_of_ne` and `Filter.liminf_eq_iSup_iInf_of_nat`). -/
theorem massWeighted_kinetic_le_liminf {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} {m : Fin N → ℝ} {c : ℝ} (hc : 0 < c) (hm : ∀ i, c ≤ m i)
    {F : ℕ → ℝ → EuclideanSpace E (Fin N)} {g : ℝ → EuclideanSpace E (Fin N)} {τ M : ℝ}
    (hτ : 0 ≤ τ) (hM : 0 ≤ M) (hg : ContinuousOn g (Set.Icc 0 τ))
    (hconv : TendstoUniformlyOn F g atTop (Set.Icc 0 τ))
    (hAC : ∀ n, AbsolutelyContinuousOnInterval (F n) 0 τ)
    (hbd : ∀ n, ∫⁻ t in Set.Ioc 0 τ,
        ENNReal.ofReal ((1 / 2) * ∑ i, m i * ‖deriv (F n) t i‖ ^ 2) ≤ ENNReal.ofReal (M ^ 2)) :
    AbsolutelyContinuousOnInterval g 0 τ ∧
      ∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal ((1 / 2) * ∑ i, m i * ‖deriv g t i‖ ^ 2)
        ≤ Filter.liminf (fun n => ∫⁻ t in Set.Ioc 0 τ,
            ENNReal.ofReal ((1 / 2) * ∑ i, m i * ‖deriv (F n) t i‖ ^ 2)) atTop := by
  have hmnonneg : ∀ i, 0 ≤ m i := fun i => le_trans hc.le (hm i)
  have hKnn : 0 ≤ Real.sqrt ((1 / 2) * ∑ i, m i) := Real.sqrt_nonneg _
  -- The mass-scaled curves inherit the hypotheses.
  have hconv_A : TendstoUniformlyOn (fun n t => massScaleCLM m (F n t))
      (fun t => massScaleCLM m (g t)) atTop (Set.Icc 0 τ) :=
    tendstoUniformlyOn_comp_dist_le hKnn (massScaleCLM_dist_le m hmnonneg) hconv
  have hg_A : ContinuousOn (fun t => massScaleCLM m (g t)) (Set.Icc 0 τ) :=
    (massScaleCLM m).continuous.comp_continuousOn hg
  have hAC_A : ∀ n, AbsolutelyContinuousOnInterval (fun t => massScaleCLM m (F n t)) 0 τ :=
    fun n => absolutelyContinuousOnInterval_comp_of_dist_le hKnn
      (massScaleCLM_dist_le m hmnonneg) (hAC n)
  -- The energy of a mass-scaled curve is the mass-weighted kinetic energy, a.e.
  have hint_n : ∀ n, ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc 0 τ →
      ENNReal.ofReal ((1 / 2) * ∑ i, m i * ‖deriv (F n) t i‖ ^ 2)
        = ENNReal.ofReal (‖deriv (fun s => massScaleCLM m (F n s)) t‖ ^ 2) := by
    intro n
    filter_upwards [ae_deriv_massScaleCLM hτ (hAC n)] with t ht htIoc
    rw [ht htIoc, massScaleCLM_norm_sq m hmnonneg]
  have hDn : ∀ n, ∫⁻ t in Set.Ioc 0 τ,
        ENNReal.ofReal ((1 / 2) * ∑ i, m i * ‖deriv (F n) t i‖ ^ 2)
      = ∫⁻ t in Set.Ioc 0 τ,
        ENNReal.ofReal (‖deriv (fun s => massScaleCLM m (F n s)) t‖ ^ 2) := by
    intro n
    exact lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioc).mpr (hint_n n))
  have hbd_A : ∀ n, ∫⁻ t in Set.Ioc 0 τ,
      ENNReal.ofReal (‖deriv (fun s => massScaleCLM m (F n s)) t‖ ^ 2)
        ≤ ENNReal.ofReal (M ^ 2) := by
    intro n
    rw [← hDn n]
    exact hbd n
  obtain ⟨hac_Ag, hineq⟩ :=
    lintegral_ofReal_sq_deriv_le_liminf (E := EuclideanSpace E (Fin N))
      hτ hM hg_A hconv_A hAC_A hbd_A
  -- Absolute continuity of `g` itself, from the non-degeneracy of the mass scaling.
  have hac_g : AbsolutelyContinuousOnInterval g 0 τ :=
    absolutelyContinuousOnInterval_of_comp_dist_le (K := (Real.sqrt ((1 / 2) * c))⁻¹)
      (by positivity) (massScaleCLM_dist_ge m hc hm) g hac_Ag
  refine ⟨hac_g, ?_⟩
  have hDg : ∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal ((1 / 2) * ∑ i, m i * ‖deriv g t i‖ ^ 2)
      = ∫⁻ t in Set.Ioc 0 τ,
        ENNReal.ofReal (‖deriv (fun s => massScaleCLM m (g s)) t‖ ^ 2) := by
    refine lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioc).mpr ?_)
    filter_upwards [ae_deriv_massScaleCLM hτ hac_g] with t ht htIoc
    rw [ht htIoc, massScaleCLM_norm_sq m hmnonneg]
  rw [hDg]
  exact hineq.trans (Filter.liminf_le_liminf (Eventually.of_forall fun n => (hDn n).ge))

end Commons.MeasureTheory.Integral
