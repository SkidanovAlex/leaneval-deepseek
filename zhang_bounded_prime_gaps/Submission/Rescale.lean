import Mathlib
import Submission.MaynardFunctionals

/-!
# Rescaling the Maynard--Polymath functionals

Polymath8a §5.1 (resp. §5.3) begins by rescaling the maximiser `F` of the variational
problem `M_k` (resp. `M_{k,ε}`) so that its support retreats from the slanted boundary of
the simplex, at an explicit cost in the functionals.  This file provides the two
elementary scaling identities

  `I(F(·/c)) = c^k · I(F)`   and   `J_i(F(·/c); cc) = c^(k+1) · J_i(F; cc/c)`,

where `F(·/c) := fun t => F (fun j => t j / c)`.
-/

open MeasureTheory Finset Filter
open scoped BigOperators

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

variable {k : ℕ}

/-- `F(·/c)`, the componentwise rescaling of `F` by `1/c`. -/
def rescale (c : ℝ) (F : (Fin k → ℝ) → ℝ) : (Fin k → ℝ) → ℝ :=
  fun t => F (fun j => t j / c)

/-- **The orthant (in fact full-space) integral scales by `c^k`.** -/
theorem IFuncOrth_rescale (c : ℝ) (hc : 0 < c) (F : (Fin k → ℝ) → ℝ) :
    IFuncOrth k (rescale c F) = c ^ k * IFuncOrth k F := by
  have h := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (μ := volume)
    (f := fun x : Fin k → ℝ => (F x) ^ 2) (R := c) hc.le
  have hfin : Module.finrank ℝ (Fin k → ℝ) = k := Module.finrank_fin_fun ℝ
  have hcongr : (fun t : Fin k → ℝ => (rescale c F t) ^ 2)
      = fun t : Fin k → ℝ => (F (c⁻¹ • t)) ^ 2 := by
    funext t
    congr 1
    refine congrArg F (funext fun j => ?_)
    simp [rescale, Pi.smul_apply, div_eq_mul_inv, mul_comm]
  unfold IFuncOrth
  rw [hcongr, h, hfin, smul_eq_mul]

/-- The marginal simplex condition scales: `t' / c` lies in the `cc/c`-simplex iff `t'`
lies in the `cc`-simplex. -/
lemma marginalSet_div_iff (c : ℝ) (hc : 0 < c) (i : Fin k) (cc : ℝ)
    (t' : {j // j ≠ i} → ℝ) :
    (fun j => t' j / c) ∈ marginalSet k i (cc / c) ↔ t' ∈ marginalSet k i cc := by
  have hsum : ∀ u : {j // j ≠ i} → ℝ, (∑ j, u j / c) = (∑ j, u j) / c :=
    fun u => (Finset.sum_div Finset.univ u c).symm
  simp only [marginalSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, ?_⟩
    · have h := h1 j
      rw [le_div_iff₀ hc] at h
      simpa using h
    · rw [hsum] at h2
      exact (div_le_div_iff_of_pos_right hc).mp h2
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => div_nonneg (h1 j) hc.le, ?_⟩
    rw [hsum]
    exact (div_le_div_iff_of_pos_right hc).mpr h2

/-- **The marginal functional scales.**  `Jᵢ` of the rescaled function at scale `cc` is
`c^(k+1)` times `Jᵢ` of the original at scale `cc / c`. -/
theorem JFunc_rescale (c : ℝ) (hc : 0 < c) (i : Fin k) (cc : ℝ) (F : (Fin k → ℝ) → ℝ) :
    JFunc k i cc (rescale c F) = c ^ (k+1) * JFunc k i (cc / c) F := by
  classical
  unfold JFunc
  have hinner : ∀ t' : {j // j ≠ i} → ℝ,
      (∫ x : ℝ, (rescale c F) (extendAt i x t'))
        = c * ∫ y : ℝ, F (extendAt i y (fun j => t' j / c)) := by
    intro t'
    have h1 : (fun x : ℝ => (rescale c F) (extendAt i x t'))
        = fun x : ℝ => F (extendAt i (x / c) (fun j => t' j / c)) := by
      funext x
      refine congrArg F (funext fun j => ?_)
      by_cases hj : j = i
      · subst hj; simp [rescale, extendAt]
      · simp [rescale, extendAt, hj]
    rw [h1]
    have h2 := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (μ := volume)
      (f := fun y : ℝ => F (extendAt i y (fun j => t' j / c))) (R := c) hc.le
    rw [Module.finrank_self, pow_one, smul_eq_mul] at h2
    rw [← h2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hpoint : ∀ t' : {j // j ≠ i} → ℝ,
      (∫ x : ℝ, (rescale c F) (extendAt i x t')) ^ 2 *
          (if t' ∈ marginalSet k i cc then (1 : ℝ) else 0)
        = c ^ 2 * ((∫ y : ℝ, F (extendAt i y (fun j => t' j / c))) ^ 2 *
          (if t' ∈ marginalSet k i cc then (1 : ℝ) else 0)) := by
    intro t'; rw [hinner t']; ring
  have hstep : (∫ t' : {j // j ≠ i} → ℝ,
        (∫ y : ℝ, F (extendAt i y (fun j => t' j / c))) ^ 2 *
          (if t' ∈ marginalSet k i cc then (1 : ℝ) else 0))
      = c ^ (k - 1) * ∫ u : {j // j ≠ i} → ℝ,
        (∫ y : ℝ, F (extendAt i y u)) ^ 2 *
          (if u ∈ marginalSet k i (cc / c) then (1 : ℝ) else 0) := by
    have h3 := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (μ := volume)
      (f := fun u : {j // j ≠ i} → ℝ =>
        (∫ y : ℝ, F (extendAt i y u)) ^ 2 *
          (if u ∈ marginalSet k i (cc / c) then (1 : ℝ) else 0)) (R := c) hc.le
    rw [Module.finrank_fintype_fun_eq_card] at h3
    simp only [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq,
      smul_eq_mul] at h3
    rw [← h3]
    refine integral_congr_ae (Eventually.of_forall fun t' => ?_)
    have hmem := marginalSet_div_iff (k := k) c hc i cc t'
    have hfun : (fun j => t' j / c) = c⁻¹ • t' := by
      funext j; simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    show (∫ y : ℝ, F (extendAt i y (fun j => t' j / c))) ^ 2 *
          (if t' ∈ marginalSet k i cc then (1 : ℝ) else 0)
        = (∫ y : ℝ, F (extendAt i y (c⁻¹ • t'))) ^ 2 *
          (if c⁻¹ • t' ∈ marginalSet k i (cc / c) then (1 : ℝ) else 0)
    rw [← hfun]
    congr 1
    exact if_congr hmem.symm rfl rfl
  rw [show (∫ t' : {j // j ≠ i} → ℝ,
        (∫ x : ℝ, (rescale c F) (extendAt i x t')) ^ 2 *
          (if t' ∈ marginalSet k i cc then (1 : ℝ) else 0))
      = ∫ t' : {j // j ≠ i} → ℝ, c ^ 2 *
        ((∫ y : ℝ, F (extendAt i y (fun j => t' j / c))) ^ 2 *
          (if t' ∈ marginalSet k i cc then (1 : ℝ) else 0))
      from integral_congr_ae (Eventually.of_forall hpoint)]
  rw [MeasureTheory.integral_const_mul, hstep, ← mul_assoc, ← pow_add,
    show (2 : ℕ) + (k - 1) = k + 1 by have := i.isLt; omega]


/-! ## Monotonicity of the marginal functional in its scale -/

/-- The total mass of `extendAt i x t'`: inserting `x` at coordinate `i` adds `x`. -/
lemma sum_extendAt {k : ℕ} (i : Fin k) (x : ℝ) (t' : {j // j ≠ i} → ℝ) :
    (∑ j : Fin k, extendAt i x t' j) = x + ∑ j : {j // j ≠ i}, t' j := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := i.isLt; omega⟩
  rw [Fin.sum_univ_succAbove (fun j : Fin (n+1) => extendAt i x t' j) i]
  have h1 : extendAt i x t' i = x := by simp [extendAt]
  have h2 : ∀ j : Fin n, extendAt i x t' (i.succAbove j)
      = t' (finSuccAboveEquiv i j) := by
    intro j
    have hne : i.succAbove j ≠ i := i.succAbove_ne j
    show (if h : i.succAbove j = i then x else t' ⟨i.succAbove j, h⟩)
        = t' (finSuccAboveEquiv i j)
    rw [dif_neg hne]
    congr 1
  rw [h1, Finset.sum_congr rfl (fun j _ => h2 j)]
  congr 1
  exact Equiv.sum_comp (finSuccAboveEquiv i) t'

/-- If `F` vanishes off the `c`-simplex then, off the `c`-marginal simplex, the line integral
`x ↦ ∫ F(extendAt i x t')` vanishes identically. -/
lemma line_integral_eq_zero_of_notMem {k : ℕ} (i : Fin k) {c : ℝ}
    {F : (Fin k → ℝ) → ℝ} (hsupp : ∀ t : Fin k → ℝ, t ∉ simplexSet k c → F t = 0)
    {t' : {j // j ≠ i} → ℝ} (ht' : t' ∉ marginalSet k i c) :
    (∫ x : ℝ, F (extendAt i x t')) = 0 := by
  refine MeasureTheory.integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
  refine hsupp _ ?_
  intro hmem
  apply ht'
  simp only [marginalSet, Set.mem_setOf_eq] at hmem ⊢
  obtain ⟨h0, hsum⟩ := hmem
  have hx : 0 ≤ x := by
    have := h0 i; rwa [extendAt, dif_pos rfl] at this
  refine ⟨fun j => ?_, ?_⟩
  · have := h0 j.val
    rwa [extendAt, dif_neg j.2] at this
  · have hse := sum_extendAt i x t'
    linarith

/-- The marginal integrand vanishes off the `c`-marginal simplex. -/
lemma marginal_integrand_eq_zero_of_notMem {k : ℕ} (i : Fin k) {c : ℝ}
    {F : (Fin k → ℝ) → ℝ} (hsupp : ∀ t : Fin k → ℝ, t ∉ simplexSet k c → F t = 0)
    {t' : {j // j ≠ i} → ℝ} (ht' : t' ∉ marginalSet k i c) :
    (∫ x : ℝ, F (extendAt i x t')) ^ 2 = 0 := by
  rw [line_integral_eq_zero_of_notMem i hsupp ht']; ring

/-- **`Jᵢ` depends on its scale only through the support.**  If `F` vanishes off the
`c`-simplex, then `Jᵢ(F)` is the same for every scale `≥ c`. -/
theorem JFunc_eq_of_le_scale {k : ℕ} (i : Fin k) {c cc : ℝ} (hcc : c ≤ cc)
    {F : (Fin k → ℝ) → ℝ} (hsupp : ∀ t : Fin k → ℝ, t ∉ simplexSet k c → F t = 0) :
    JFunc k i cc F = JFunc k i c F := by
  unfold JFunc
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun t' => ?_)
  by_cases ht : t' ∈ marginalSet k i c
  · have ht2 : t' ∈ marginalSet k i cc := by
      simp only [marginalSet, Set.mem_setOf_eq] at ht ⊢; exact ⟨ht.1, le_trans ht.2 hcc⟩
    simp only [ht, ht2, if_true]
  · have hz : (∫ x : ℝ, F (extendAt i x t')) = 0 := line_integral_eq_zero_of_notMem i hsupp ht
    by_cases ht2 : t' ∈ marginalSet k i cc
    · simp [ht, ht2, hz]
    · simp [ht, ht2]

/-! ## The rescaling step of Polymath8a §5.1 -/

/-- The Rayleigh quotient of the `ε`-enlarged variational problem. -/
noncomputable def ratio (k : ℕ) (ε : ℝ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  (∑ i : Fin k, JFunc k i (1 - ε) F) / IFuncOrth k F

/-- The quotient at a shifted marginal scale. -/
noncomputable def ratioOfScale (k : ℕ) (ε : ℝ) (lam : ℝ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  (∑ i : Fin k, JFunc k i ((1 - ε) / lam) F) / IFuncOrth k F

/-- **Scaling the argument by `1/λ` multiplies the Rayleigh quotient by `λ`** (at the
correspondingly rescaled marginal scale). -/
theorem ratio_rescale {k : ℕ} (ε lam : ℝ) (hlam : 0 < lam) (F : (Fin k → ℝ) → ℝ) :
    ratio k ε (rescale lam F) = lam * ratioOfScale k ε lam F := by
  unfold ratio ratioOfScale
  rw [IFuncOrth_rescale lam hlam F]
  rw [Finset.sum_congr rfl (fun i _ => JFunc_rescale lam hlam i (1 - ε) F)]
  rw [← Finset.mul_sum]
  have hpow : lam ^ k ≠ 0 := pow_ne_zero _ (ne_of_gt hlam)
  rw [pow_succ]
  rcases eq_or_ne (IFuncOrth k F) 0 with hI | hI
  · rw [hI, mul_zero, div_zero, div_zero, mul_zero]
  · field_simp

/-! ## The marginal set is closed; monotonicity of `Jᵢ` in the scale (`§5.1`, second half) -/

/-- The total-mass function on the marginal coordinates. -/
lemma continuous_marginalSum {k : ℕ} (i : Fin k) :
    Continuous (fun t' : {j : Fin k // j ≠ i} → ℝ => ∑ j, t' j) := by
  fun_prop

/-- `marginalSet k i c` is closed (an intersection of closed half-spaces). -/
lemma isClosed_marginalSet (k : ℕ) (i : Fin k) (c : ℝ) : IsClosed (marginalSet k i c) := by
  have hset : marginalSet k i c
      = (⋂ j : {j : Fin k // j ≠ i}, {t' | 0 ≤ t' j}) ∩ {t' | (∑ j, t' j) ≤ c} := by
    ext t'
    simp only [marginalSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  exact IsClosed.inter (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j))
    (isClosed_le (continuous_marginalSum i) continuous_const)

lemma measurableSet_marginalSet (k : ℕ) (i : Fin k) (c : ℝ) :
    MeasurableSet (marginalSet k i c) :=
  (isClosed_marginalSet k i c).measurableSet

/-- `Jᵢ(F; c)` is the *set integral* of the squared line integral over the marginal simplex. -/
lemma JFunc_eq_setIntegral {k : ℕ} (i : Fin k) (c : ℝ) (F : (Fin k → ℝ) → ℝ) :
    JFunc k i c F
      = ∫ t' in marginalSet k i c, (∫ x : ℝ, F (extendAt i x t')) ^ 2 := by
  classical
  rw [JFunc]
  rw [← integral_indicator (measurableSet_marginalSet k i c)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t' => ?_)
  by_cases h : t' ∈ marginalSet k i c
  · rw [Set.indicator_of_mem h]; simp only [h, if_true, mul_one]
  · rw [Set.indicator_of_notMem h]; simp only [h, if_false, mul_zero]

/-- **Monotonicity of `Jᵢ` in its scale.**  For `c₁ ≤ c₂` the pointwise-nonnegative integrand
`(∫ x, F(extendAt i x ·))²` has a smaller integral over the smaller marginal simplex, provided
that it is integrable over the larger one (the proviso is needed only because the Bochner
integral of a non-integrable function is `0` by convention). -/
theorem JFunc_mono {k : ℕ} (i : Fin k) {c₁ c₂ : ℝ} (hcc : c₁ ≤ c₂)
    (F : (Fin k → ℝ) → ℝ)
    (hint : MeasureTheory.IntegrableOn (fun t' : {j : Fin k // j ≠ i} → ℝ =>
      (∫ x : ℝ, F (extendAt i x t')) ^ 2) (marginalSet k i c₂) volume) :
    JFunc k i c₁ F ≤ JFunc k i c₂ F := by
  rw [JFunc_eq_setIntegral, JFunc_eq_setIntegral]
  have hsub : marginalSet k i c₁ ⊆ marginalSet k i c₂ :=
    fun t' ht' => ⟨ht'.1, le_trans ht'.2 hcc⟩
  exact setIntegral_mono_set hint (Filter.Eventually.of_forall fun t' => sq_nonneg _)
    (Filter.Eventually.of_forall fun t' ht' => hsub ht')

/-- The `Integrable`-version of `JFunc_mono`. -/
theorem JFunc_mono_of_integrable {k : ℕ} (i : Fin k) {c₁ c₂ : ℝ} (hcc : c₁ ≤ c₂)
    (F : (Fin k → ℝ) → ℝ)
    (hint : Integrable (fun t' : {j : Fin k // j ≠ i} → ℝ =>
      (∫ x : ℝ, F (extendAt i x t')) ^ 2)) :
    JFunc k i c₁ F ≤ JFunc k i c₂ F :=
  JFunc_mono i hcc F hint.integrableOn

/-- **The rescaling inequality of Polymath8a §5.1.**  If `0 < λ ≤ 1` and `F` is supported on
the `(1+ε)`-simplex, then rescaling `F` by `1/λ` multiplies its Rayleigh quotient by at least
`λ`:

  `ratio k ε (rescale λ F) ≥ λ · ratio k ε F`.

This is the step that turns `ΣᵢJ_{i,1-ε}(F)/I(F) > 2m/ϑ` into `> m` for the rescaled
function of support `(ϑ/2 - δ₁)·Rᵏ`. -/
theorem ratio_rescale_ge (k : ℕ) (ε lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hε : ε ≤ 1) (F : (Fin k → ℝ) → ℝ) (hI : 0 < IFuncOrth k F)
    (hint : ∀ i : Fin k, MeasureTheory.IntegrableOn (fun t' : {j : Fin k // j ≠ i} → ℝ =>
      (∫ x : ℝ, F (extendAt i x t')) ^ 2) (marginalSet k i ((1 - ε) / lam)) volume) :
    lam * ratio k ε F ≤ ratio k ε (rescale lam F) := by
  rw [ratio_rescale ε lam hlam0 F]
  have hcc : 1 - ε ≤ (1 - ε) / lam := by
    rw [le_div_iff₀ hlam0]
    nlinarith
  have hsum : (∑ i : Fin k, JFunc k i (1 - ε) F)
      ≤ ∑ i : Fin k, JFunc k i ((1 - ε) / lam) F :=
    Finset.sum_le_sum fun i _ => JFunc_mono i hcc F (hint i)
  have hIle : 0 ≤ IFuncOrth k F := le_of_lt hI
  have h1 : ratio k ε F ≤ ratioOfScale k ε lam F := by
    rw [ratio, ratioOfScale]
    exact div_le_div_of_nonneg_right hsum hIle
  exact mul_le_mul_of_nonneg_left h1 (le_of_lt hlam0)

/-! ## The marginal scale-`c` Rayleigh quotient, and the truncating-rescaling step of §5.1 -/

/-- The Rayleigh quotient of the variational problem at a *general* marginal scale `c`
(`c = 1 - ε` is `ratio`, `c = (1-ε)ϑ/2` is the sieve scale of Polymath8a §5.3). -/
noncomputable def ratioScale (k : ℕ) (c : ℝ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  (∑ i : Fin k, JFunc k i c F) / IFuncOrth k F

lemma ratio_eq_ratioScale (k : ℕ) (ε : ℝ) (F : (Fin k → ℝ) → ℝ) :
    ratio k ε F = ratioScale k (1 - ε) F := rfl

/-- The scaling law for the general-scale quotient:
`ratioScale k c (rescale λ F) = λ · ratioScale k (c/λ) F`. -/
theorem ratioScale_rescale (k : ℕ) (c lam : ℝ) (hlam : 0 < lam) (F : (Fin k → ℝ) → ℝ) :
    ratioScale k c (rescale lam F) = lam * ratioScale k (c / lam) F := by
  unfold ratioScale
  rw [IFuncOrth_rescale lam hlam F]
  rw [Finset.sum_congr rfl (fun i _ => JFunc_rescale lam hlam i c F)]
  rw [← Finset.mul_sum]
  have hpow : lam ^ k ≠ 0 := pow_ne_zero _ (ne_of_gt hlam)
  rw [pow_succ]
  rcases eq_or_ne (IFuncOrth k F) 0 with hI | hI
  · rw [hI, mul_zero, div_zero, div_zero, mul_zero]
  · field_simp

/-- The scaling inequality for the general-scale quotient: if `0 < λ ≤ 1` and the line integrals
of `F` are square-integrable (so that `Jᵢ` is honest), then
`λ · ratioScale k c F ≤ ratioScale k c (rescale λ F)` whenever `0 ≤ c ≤ c/λ`
(i.e. `1 - ε ≤ (1-ε)ϑ/(2λ)`, the pairing used in §5.3). -/
theorem ratioScale_rescale_ge (k : ℕ) (c lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hc : 0 ≤ c) (F : (Fin k → ℝ) → ℝ) (hI : 0 < IFuncOrth k F)
    (hint : ∀ i : Fin k, Integrable (fun t' : {j : Fin k // j ≠ i} → ℝ =>
      (∫ x : ℝ, F (extendAt i x t')) ^ 2)) :
    lam * ratioScale k c F ≤ ratioScale k c (rescale lam F) := by
  rw [ratioScale_rescale k c lam hlam0 F]
  have hcc : c ≤ c / lam := by
    rw [le_div_iff₀ hlam0]; nlinarith
  have hsum : (∑ i : Fin k, JFunc k i c F) ≤ ∑ i : Fin k, JFunc k i (c / lam) F :=
    Finset.sum_le_sum fun i _ => JFunc_mono_of_integrable i hcc F (hint i)
  have hIle : 0 ≤ IFuncOrth k F := le_of_lt hI
  have h1 : ratioScale k c F ≤ ratioScale k (c / lam) F := by
    rw [ratioScale, ratioScale]
    exact div_le_div_of_nonneg_right hsum hIle
  exact mul_le_mul_of_nonneg_left h1 (le_of_lt hlam0)

/-- **The truncating–rescaling step of Polymath8a §5.1/§5.3.**  Suppose `F` carries the
variational lower bound `ΣᵢJ_{i,1-ε}(F)/I(F) > 2m/ϑ`.  Then for the marginal scale
`c = (1-ε)ϑ/2` of the sieve there is a rescaling `F(·/λ)` (`0 < λ ≤ ϑ/2`) whose *sieve-scale*
quotient still exceeds `m`. -/
theorem exists_ratioScale_rescale_gt {k : ℕ} (ε ϑ m : ℝ) (hϑ : 0 < ϑ) (hm : 0 < m)
    (hε : ε ≤ 1) (F : (Fin k → ℝ) → ℝ) (hI : 0 < IFuncOrth k F)
    (hratio : 2 * m / ϑ < ratioScale k (1 - ε) F)
    (hint : ∀ i : Fin k, Integrable (fun t' : {j : Fin k // j ≠ i} → ℝ =>
      (∫ x : ℝ, F (extendAt i x t')) ^ 2)) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ ϑ / 2 ∧
      m < ratioScale k ((1 - ε) * (ϑ / 2)) (rescale lam F) := by
  have hrpos : 0 < ratioScale k (1 - ε) F := by
    have h1 : 0 < 2 * m / ϑ := div_pos (by linarith) hϑ
    linarith
  have h2m : 2 * m < ratioScale k (1 - ε) F * ϑ := by
    have h := (div_lt_iff₀ hϑ).mp hratio
    linarith
  have hmr : m / ratioScale k (1 - ε) F < ϑ / 2 := by
    rw [div_lt_iff₀ hrpos]
    linarith
  have hmrpos : 0 < m / ratioScale k (1 - ε) F := div_pos hm hrpos
  set lam : ℝ := (m / ratioScale k (1 - ε) F + ϑ / 2) / 2 with hlamdef
  have hlam0 : 0 < lam := by rw [hlamdef]; linarith
  have hlamle : lam ≤ ϑ / 2 := by rw [hlamdef]; linarith
  refine ⟨lam, hlam0, hlamle, ?_⟩
  have hgt : m < lam * ratioScale k (1 - ε) F := by
    rw [hlamdef]
    have h1 : (m / ratioScale k (1 - ε) F + ϑ / 2) / 2 * ratioScale k (1 - ε) F
        = (m + ϑ / 2 * ratioScale k (1 - ε) F) / 2 := by
      field_simp
    rw [h1]
    have h2 : m < ϑ / 2 * ratioScale k (1 - ε) F := by linarith
    linarith
  have hstep : ratioScale k ((1 - ε) * (ϑ / 2)) (rescale lam F)
      = lam * ratioScale k (((1 - ε) * (ϑ / 2)) / lam) F :=
    ratioScale_rescale k _ lam hlam0 F
  rw [hstep]
  have hcc : 1 - ε ≤ ((1 - ε) * (ϑ / 2)) / lam := by
    rw [le_div_iff₀ hlam0, hlamdef]
    nlinarith [hmr, hmrpos]
  have hsum : (∑ i : Fin k, JFunc k i (1 - ε) F)
      ≤ ∑ i : Fin k, JFunc k i (((1 - ε) * (ϑ / 2)) / lam) F :=
    Finset.sum_le_sum fun i _ => JFunc_mono_of_integrable i hcc F (hint i)
  have h3 : ratioScale k (1 - ε) F ≤ ratioScale k (((1 - ε) * (ϑ / 2)) / lam) F := by
    rw [ratioScale, ratioScale]
    exact div_le_div_of_nonneg_right hsum (le_of_lt hI)
  calc m < lam * ratioScale k (1 - ε) F := hgt
    _ ≤ lam * ratioScale k (((1 - ε) * (ϑ / 2)) / lam) F :=
        mul_le_mul_of_nonneg_left h3 (le_of_lt hlam0)

/-- If `F` vanishes off the `c`-simplex then its `λ`-rescaling vanishes off the `λc`-simplex. -/
theorem rescale_eq_zero_of_notMem {k : ℕ} (lam c : ℝ) (hlam : 0 < lam)
    {F : (Fin k → ℝ) → ℝ} (hsupp : ∀ t : Fin k → ℝ, t ∉ simplexSet k c → F t = 0)
    {t : Fin k → ℝ} (ht : t ∉ simplexSet k (lam * c)) : rescale lam F t = 0 := by
  refine hsupp _ ?_
  intro hmem
  apply ht
  have h1 : ∀ j : Fin k, 0 ≤ t j / lam := hmem.1
  have h2 : (∑ j : Fin k, t j / lam) ≤ c := hmem.2
  have hsum : (∑ j : Fin k, t j / lam) = (∑ j : Fin k, t j) / lam :=
    (Finset.sum_div Finset.univ (fun j => t j) lam).symm
  have ht_nonneg : ∀ j : Fin k, 0 ≤ t j := by
    intro j
    have h := mul_nonneg (h1 j) hlam.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hlam)] at h
  rw [hsum, div_le_iff₀ hlam, mul_comm] at h2
  exact ⟨ht_nonneg, h2⟩

end

end Commons.NumberTheory.MaynardSieve
