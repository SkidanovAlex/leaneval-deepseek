import Mathlib
import Submission.Work.Noncompact.CompressionTube.collar_defs

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# Blending two transverse functions with the same derivative on a line

Let `M` be a smooth `n`-manifold (`n ≥ 2`), `γ : ℝ → M` a line, `g : M → ℝ` a smooth function
with `g (γ s) = s`, and `G₁, G₂ : M → ℝ^{n-1}` two smooth functions vanishing on the line whose
derivatives *agree* at `γ s₁`.  This file proves `exists_transverse_blend`: if `G₁` is transverse
to `g` at `γ s₁`, then so is *every* smooth blend `χ (g ·) • G₁ + (1 - χ (g ·)) • G₂` with
`χ : ℝ → [0,1]`, uniformly for `s` near `s₁`.

The mathematical content is:

* at `x = γ s` the derivative of the blend is `χ s • dG₁ (γ s) + (1 - χ s) • dG₂ (γ s)` (the
  `χ'`-term carries the factor `G₁ (γ s) - G₂ (γ s) = 0`);
* at `s = s₁` the two derivatives coincide (`hagree`), so the blend has the *same* derivative
  `L := dG₁ (γ s₁)` as `G₁` for every value of `χ`; hence transversality at `s₁` for all blends;
* injectivity of `L` on `ker (dg (γ s₁))` is stable under small perturbations of the pair
  `(L, dg)`, *uniformly* in the interpolation parameter `t ∈ [0,1]`
  (`exists_uniform_blend_injective`, a finite-dimensional compactness statement);
* the coordinate expression of the blended map in a chart at `γ s₁` has derivative
  `t • fderiv A y + (1 - t) • fderiv B y` with `A = G₁ ∘ c.symm`, `B = G₂ ∘ c.symm` and `t = χ (s)`
  (product rule, using `A y = B y = 0`), and the coordinate functions' derivatives are continuous
  in `y`.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## A chain rule for the chart expression of a smooth map -/

/-- The coordinate expression `y ↦ ψ (c.symm y)` of a smooth `ψ : M → E'` in a chart `c` of `M`
has derivative `dψ ∘ d(c.symm)`; this is the manifold chain rule, rewritten in terms of `fderiv`
because the model spaces carry their self model-with-corners. -/
theorem hasFDerivAt_coord {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {ψ : M → E'}
    (hψ : ContMDiff (MC n) (𝓘(ℝ, E')) smoothOrder ψ)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ c.target) :
    HasFDerivAt (fun y' => ψ (c.symm y'))
      ((mfderiv (MC n) (𝓘(ℝ, E')) ψ (c.symm y)).comp
        (mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) y)) y := by
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  have hsymm : ContMDiffAt (MC n) (MC n) smoothOrder
      (c.symm : EuclideanSpace ℝ (Fin n) → M) y :=
    contMDiffAt_symm_of_mem_maximalAtlas hc hy
  have hsymm_md : MDifferentiableAt (MC n) (MC n)
      (c.symm : EuclideanSpace ℝ (Fin n) → M) y := hsymm.mdifferentiableAt hn0
  exact hasMFDerivAt_iff_hasFDerivAt.mp
    ((hψ.mdifferentiableAt (x := c.symm y) hn0).hasMFDerivAt.comp y hsymm_md.hasMFDerivAt)

/-! ## The finite-dimensional openness input -/

/-- **Uniform injectivity of the blends.**  Let `E` be a finite-dimensional real normed space and
let `L : E → F`, `M : E → ℝ` be continuous linear maps whose common kernel is trivial
(`M v = 0 → L v = 0 → v = 0`).  Then all maps `t • L₁ + (1 - t) • L₂` with `t ∈ [0,1]` are
injective on `ker M'`, uniformly for `(L₁, L₂, M')` in a neighbourhood of `(L, L, M)`. -/
theorem exists_uniform_blend_injective {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (M : E →L[ℝ] ℝ)
    (h : ∀ v : E, M v = 0 → L v = 0 → v = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (L₁ L₂ : E →L[ℝ] F) (M' : E →L[ℝ] ℝ),
      ‖L₁ - L‖ < ε → ‖L₂ - L‖ < ε → ‖M' - M‖ < ε →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v : E, M' v = 0 →
        (t • L₁ + (1 - t) • L₂) v = 0 → v = 0 := by
  have hpair : Function.Injective (fun v : E => (L v, M v)) := by
    intro v w hvw
    have h1 : L v = L w := congrArg Prod.fst hvw
    have h2 : M v = M w := congrArg Prod.snd hvw
    have h1' : L (v - w) = 0 := by rw [map_sub, h1, sub_self]
    have h2' : M (v - w) = 0 := by rw [map_sub, h2, sub_self]
    exact sub_eq_zero.mp (h (v - w) h2' h1')
  set φ : E → ℝ := fun v => max ‖L v‖ ‖M v‖ with hφ
  have hφc : Continuous φ := (L.continuous.norm).max (M.continuous.norm)
  have hφpos : ∀ v : E, v ≠ 0 → 0 < φ v := by
    intro v hv
    have hLle : ‖L v‖ ≤ φ v := by
      rw [hφ]; simp only []; exact le_max_left _ _
    have hMle : ‖M v‖ ≤ φ v := by
      rw [hφ]; simp only []; exact le_max_right _ _
    have hφnn : 0 ≤ φ v := (norm_nonneg (L v)).trans hLle
    have hne : φ v ≠ 0 := by
      intro h0
      have hL0 : L v = 0 := norm_eq_zero.mp (le_antisymm (h0 ▸ hLle) (norm_nonneg _))
      have hM0 : M v = 0 := norm_eq_zero.mp (le_antisymm (h0 ▸ hMle) (norm_nonneg _))
      exact hv (h v hM0 hL0)
    exact lt_of_le_of_ne hφnn (Ne.symm hne)
  -- the minimum of `φ` on the unit sphere
  have hsphere : (Metric.sphere (0 : E) 1).Nonempty := by
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    refine ⟨‖v‖⁻¹ • v, ?_⟩
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hsphere hφc.continuousOn
  have hv₀ne : v₀ ≠ 0 := by
    intro h0
    rw [h0, Metric.mem_sphere, dist_self] at hv₀
    norm_num at hv₀
  have hcpos : 0 < φ v₀ := hφpos v₀ hv₀ne
  -- homogeneity and the lower bound
  have hhom : ∀ (t : ℝ) (v : E), 0 ≤ t → φ (t • v) = t * φ v := by
    intro t v ht
    have ht' : ‖t‖ = t := Real.norm_of_nonneg ht
    rw [hφ]
    simp only [map_smul, norm_smul, ht']
    rw [mul_max_of_nonneg _ _ ht]
  have hbound : ∀ v : E, φ v₀ * ‖v‖ ≤ φ v := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp only [norm_zero, mul_zero]
      rw [hφ]; simp
    · have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hnorm : ‖‖v‖⁻¹ • v‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
          inv_mul_cancel₀ hvn]
      have h1 : φ v = ‖v‖ * φ (‖v‖⁻¹ • v) := by
        conv_lhs => rw [← smul_inv_smul₀ hvn v]
        rw [hhom ‖v‖ _ (norm_nonneg v)]
      have hmem : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : E) 1 := by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero, hnorm]
      rw [h1]
      calc φ v₀ * ‖v‖ = ‖v‖ * φ v₀ := by ring
        _ ≤ ‖v‖ * φ (‖v‖⁻¹ • v) := mul_le_mul_of_nonneg_left (hmin hmem) (norm_nonneg v)
  refine ⟨φ v₀ / 2, by linarith, ?_⟩
  intro L₁ L₂ M' h₁ h₂ h₃ t ht v hvM hvblend
  by_contra hvne
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have hε1 : ‖L - L₁‖ ≤ φ v₀ / 2 := by rw [norm_sub_rev]; exact le_of_lt h₁
  have hε2 : ‖L - L₂‖ ≤ φ v₀ / 2 := by rw [norm_sub_rev]; exact le_of_lt h₂
  have hεM : ‖M - M'‖ ≤ φ v₀ / 2 := by rw [norm_sub_rev]; exact le_of_lt h₃
  have key1 : ‖L v‖ ≤ φ v₀ / 2 * ‖v‖ := by
    have hsplit : L v - (t • L₁ + (1 - t) • L₂) v
        = t • ((L - L₁) v) + (1 - t) • ((L - L₂) v) := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_sub, smul_add]
      module
    calc ‖L v‖ = ‖L v - (t • L₁ + (1 - t) • L₂) v‖ := by rw [hvblend, sub_zero]
      _ = ‖t • ((L - L₁) v) + (1 - t) • ((L - L₂) v)‖ := by rw [hsplit]
      _ ≤ ‖t • ((L - L₁) v)‖ + ‖(1 - t) • ((L - L₂) v)‖ := norm_add_le _ _
      _ = t * ‖(L - L₁) v‖ + (1 - t) * ‖(L - L₂) v‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ht.1,
          Real.norm_of_nonneg (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)]
      _ ≤ t * (φ v₀ / 2 * ‖v‖) + (1 - t) * (φ v₀ / 2 * ‖v‖) := by
        have hb1 : ‖(L - L₁) v‖ ≤ φ v₀ / 2 * ‖v‖ :=
          le_trans ((L - L₁).le_opNorm v) (mul_le_mul_of_nonneg_right hε1 (norm_nonneg v))
        have hb2 : ‖(L - L₂) v‖ ≤ φ v₀ / 2 * ‖v‖ :=
          le_trans ((L - L₂).le_opNorm v) (mul_le_mul_of_nonneg_right hε2 (norm_nonneg v))
        have h1t : 0 ≤ 1 - t := by linarith [ht.2]
        exact add_le_add (mul_le_mul_of_nonneg_left hb1 ht.1)
          (mul_le_mul_of_nonneg_left hb2 h1t)
      _ = φ v₀ / 2 * ‖v‖ := by ring
  have key2 : ‖M v‖ ≤ φ v₀ / 2 * ‖v‖ := by
    calc ‖M v‖ = ‖M v - M' v‖ := by rw [hvM, sub_zero]
      _ = ‖(M - M') v‖ := rfl
      _ ≤ ‖M - M'‖ * ‖v‖ := (M - M').le_opNorm v
      _ ≤ φ v₀ / 2 * ‖v‖ := mul_le_mul_of_nonneg_right hεM (norm_nonneg v)
  have hupper : φ v ≤ φ v₀ / 2 * ‖v‖ := by
    rw [hφ]
    exact max_le key1 key2
  have hlower := hbound v
  nlinarith [hlower, hupper, hvpos, hcpos]

/-! ## The derivative of the blended coordinate expression -/

/-- **Product rule for the blended coordinate expression.**  If `A = G₁ ∘ c.symm`, `B = G₂ ∘ c.symm`
both vanish at `y`, then the coordinate expression of `χ (g ·) • G₁ + (1 - χ (g ·)) • G₂` has
derivative `χ (g (c.symm y)) • dA + (1 - χ (g (c.symm y))) • dB` at `y`: the `χ'`-terms carry the
factor `A y - B y = 0`. -/
theorem fderiv_blend_coord {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ smoothOrder χ)
    {g : M → ℝ} (hg : ContMDiff (MC n) MCreal smoothOrder g)
    {G₁ G₂ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hG₁ : ContMDiff (MC n) (MC (n - 1)) smoothOrder G₁)
    (hG₂ : ContMDiff (MC n) (MC (n - 1)) smoothOrder G₂)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ c.target)
    (hA : G₁ (c.symm y) = 0) (hB : G₂ (c.symm y) = 0) :
    fderiv ℝ (fun y' => χ (g (c.symm y')) • G₁ (c.symm y')
        + (1 - χ (g (c.symm y'))) • G₂ (c.symm y')) y
      = χ (g (c.symm y)) • fderiv ℝ (fun y' => G₁ (c.symm y')) y
        + (1 - χ (g (c.symm y))) • fderiv ℝ (fun y' => G₂ (c.symm y')) y := by
  set A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - 1)) :=
    fun y' => G₁ (c.symm y') with hAdef
  set B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - 1)) :=
    fun y' => G₂ (c.symm y') with hBdef
  set Γ : EuclideanSpace ℝ (Fin n) → ℝ := fun y' => g (c.symm y') with hΓdef
  have hAdiff : DifferentiableAt ℝ A y := (hasFDerivAt_coord (n := n) hG₁ hc hy).differentiableAt
  have hBdiff : DifferentiableAt ℝ B y := (hasFDerivAt_coord (n := n) hG₂ hc hy).differentiableAt
  have hΓdiff : DifferentiableAt ℝ Γ y := (hasFDerivAt_coord (n := n) hg hc hy).differentiableAt
  have hχdiff : DifferentiableAt ℝ χ (Γ y) :=
    (hχ.differentiable (by simp [smoothOrder])).differentiableAt
  have hc₁diff : DifferentiableAt ℝ (fun y' => χ (Γ y')) y := hχdiff.comp y hΓdiff
  have hc₂diff : DifferentiableAt ℝ (fun y' => 1 - χ (Γ y')) y :=
    (differentiableAt_const (1 : ℝ)).sub hc₁diff
  have hd1 : DifferentiableAt ℝ (fun y' => χ (Γ y') • A y') y := hc₁diff.smul hAdiff
  have hd2 : DifferentiableAt ℝ (fun y' => (1 - χ (Γ y')) • B y') y := hc₂diff.smul hBdiff
  have hsplit : (fun y' => χ (Γ y') • A y' + (1 - χ (Γ y')) • B y')
      = (fun y' => χ (Γ y') • A y') + (fun y' => (1 - χ (Γ y')) • B y') := by
    funext y'; rfl
  have hA0 : A y = 0 := by rw [hAdef]; exact hA
  have hB0 : B y = 0 := by rw [hBdef]; exact hB
  rw [hsplit, fderiv_add hd1 hd2, fderiv_fun_smul hc₁diff hAdiff,
    fderiv_fun_smul hc₂diff hBdiff, hA0, hB0, ContinuousLinearMap.smulRight_zero,
    ContinuousLinearMap.smulRight_zero, add_zero, add_zero, hAdef, hBdef, hΓdef]

/-! ## The main result -/

set_option maxHeartbeats 2000000 in
theorem exists_transverse_blend {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {γ : ℝ → M} (hγ : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder γ) (hinj : Function.Injective γ)
    (hprop : IsProperMap γ) (himm : ∀ s : ℝ, Function.Injective (mfderiv
      Work.Noncompact.CompressionTube.MCreal (Work.Noncompact.CompressionTube.MC n) γ s))
    {g : M → ℝ} (hg : ContMDiff (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.MCreal Work.Noncompact.CompressionTube.smoothOrder g)
    (hgcore : ∀ s : ℝ, g (γ s) = s)
    {G₁ G₂ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hG₁ : ContMDiff (Work.Noncompact.CompressionTube.MC n)
      (Work.Noncompact.CompressionTube.MC (n - 1))
      Work.Noncompact.CompressionTube.smoothOrder G₁)
    (hG₂ : ContMDiff (Work.Noncompact.CompressionTube.MC n)
      (Work.Noncompact.CompressionTube.MC (n - 1))
      Work.Noncompact.CompressionTube.smoothOrder G₂)
    (hv₁ : ∀ s : ℝ, G₁ (γ s) = 0) (hv₂ : ∀ s : ℝ, G₂ (γ s) = 0)
    {s₁ : ℝ}
    (hagree : mfderiv (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.MC (n - 1)) G₁ (γ s₁) =
      mfderiv (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.MC (n - 1)) G₂ (γ s₁))
    (htrans : Work.Noncompact.CompressionTube.Transverse γ g G₁ s₁) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (χ : ℝ → ℝ), ContDiff ℝ Work.Noncompact.CompressionTube.smoothOrder χ →
      (∀ t : ℝ, χ t ∈ Set.Icc 0 1) → ∀ s : ℝ, |s - s₁| < ρ →
        Work.Noncompact.CompressionTube.Transverse γ g
          (fun x : M => χ (g x) • G₁ x + (1 - χ (g x)) • G₂ x) s := by
  classical
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  -- the chart at `γ s₁`
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) (γ s₁) with hcdef
  have hcm : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas (γ s₁)
  have hmd : c.MDifferentiable (MC n) (MC n) := mdifferentiable_chart (γ s₁)
  have hcsrc : γ s₁ ∈ c.source := mem_chart_source _ (γ s₁)
  have hy₁t : c (γ s₁) ∈ c.target := c.map_source hcsrc
  have hy₁t' : c (γ s₁) ∈ c.symm.source := by rwa [OpenPartialHomeomorph.symm_source]
  -- the coordinate expressions of `G₁`, `G₂`, `g`
  set A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - 1)) :=
    fun y => G₁ (c.symm y) with hAdef
  set B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - 1)) :=
    fun y => G₂ (c.symm y) with hBdef
  set Γ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => g (c.symm y) with hΓdef
  -- the manifold derivatives at the base point, with concrete types
  let Se₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s₁))
  let L₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) G₁ (γ s₁)
  let L₂ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) G₂ (γ s₁)
  let Lg₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := mfderiv (MC n) MCreal g (γ s₁)
  have hSeInj : Function.Injective Se₁ := (hmd.symm.mfderiv hy₁t').injective
  have hAder : fderiv ℝ A (c (γ s₁)) = L₁.comp Se₁ := by
    have h := (hasFDerivAt_coord (n := n) hG₁ hcm hy₁t).fderiv
    rw [c.left_inv hcsrc] at h
    rw [hAdef]
    exact h
  have hBder : fderiv ℝ B (c (γ s₁)) = L₂.comp Se₁ := by
    have h := (hasFDerivAt_coord (n := n) hG₂ hcm hy₁t).fderiv
    rw [c.left_inv hcsrc] at h
    rw [hBdef]
    exact h
  have hΓder : fderiv ℝ Γ (c (γ s₁)) = Lg₁.comp Se₁ := by
    have h := (hasFDerivAt_coord (n := n) hg hcm hy₁t).fderiv
    rw [c.left_inv hcsrc] at h
    rw [hΓdef]
    exact h
  -- the transversality hypothesis at the base point, in coordinates
  have hL12 : L₁ = L₂ := hagree
  have hBA : fderiv ℝ B (c (γ s₁)) = fderiv ℝ A (c (γ s₁)) := by
    rw [hBder, hAder, hL12]
  have hbase : ∀ δ : EuclideanSpace ℝ (Fin n),
      fderiv ℝ Γ (c (γ s₁)) δ = 0 → fderiv ℝ A (c (γ s₁)) δ = 0 → δ = 0 := by
    intro δ h1 h2
    rw [hΓder] at h1
    rw [hAder] at h2
    change Lg₁ (Se₁ δ) = 0 at h1
    change L₁ (Se₁ δ) = 0 at h2
    have h3 : Se₁ δ = 0 := htrans (Se₁ δ) h2 h1
    exact hSeInj (by rw [h3, map_zero])
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    infer_instance
  obtain ⟨ε, hεpos, hεprop⟩ :=
    exists_uniform_blend_injective (fderiv ℝ A (c (γ s₁))) (fderiv ℝ Γ (c (γ s₁))) hbase
  -- continuity of the derivative of the coordinate expressions
  have hsymmb : ContMDiffAt (MC n) (MC n) smoothOrder
      (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s₁)) :=
    contMDiffAt_symm_of_mem_maximalAtlas hcm hy₁t
  have hAcd : ContDiffAt ℝ smoothOrder A (c (γ s₁)) := by
    have h1 : ContMDiffAt (MC n) (MC (n - 1)) smoothOrder
        (fun y => G₁ (c.symm y)) (c (γ s₁)) :=
      (hG₁.contMDiffAt (x := c.symm (c (γ s₁)))).comp (c (γ s₁)) hsymmb
    rw [hAdef]
    exact h1.contDiffAt
  have hBcd : ContDiffAt ℝ smoothOrder B (c (γ s₁)) := by
    have h1 : ContMDiffAt (MC n) (MC (n - 1)) smoothOrder
        (fun y => G₂ (c.symm y)) (c (γ s₁)) :=
      (hG₂.contMDiffAt (x := c.symm (c (γ s₁)))).comp (c (γ s₁)) hsymmb
    rw [hBdef]
    exact h1.contDiffAt
  have hΓcd : ContDiffAt ℝ smoothOrder Γ (c (γ s₁)) := by
    have h1 : ContMDiffAt (MC n) MCreal smoothOrder
        (fun y => g (c.symm y)) (c (γ s₁)) :=
      (hg.contMDiffAt (x := c.symm (c (γ s₁)))).comp (c (γ s₁)) hsymmb
    rw [hΓdef]
    exact h1.contDiffAt
  have hAcont : ContinuousAt (fderiv ℝ A) (c (γ s₁)) := hAcd.continuousAt_fderiv hn0
  have hBcont : ContinuousAt (fderiv ℝ B) (c (γ s₁)) := hBcd.continuousAt_fderiv hn0
  have hΓcont : ContinuousAt (fderiv ℝ Γ) (c (γ s₁)) := hΓcd.continuousAt_fderiv hn0
  -- a neighbourhood of the base point on which all the blends are injective
  have hnhds : ∀ᶠ y in 𝓝 (c (γ s₁)),
      ‖fderiv ℝ A y - fderiv ℝ A (c (γ s₁))‖ < ε ∧
      ‖fderiv ℝ B y - fderiv ℝ A (c (γ s₁))‖ < ε ∧
      ‖fderiv ℝ Γ y - fderiv ℝ Γ (c (γ s₁))‖ < ε := by
    have h1 : ∀ᶠ y in 𝓝 (c (γ s₁)), ‖fderiv ℝ A y - fderiv ℝ A (c (γ s₁))‖ < ε := by
      have hb := hAcont.preimage_mem_nhds (Metric.ball_mem_nhds (fderiv ℝ A (c (γ s₁))) hεpos)
      filter_upwards [hb] with y hy
      rwa [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hy
    have h2 : ∀ᶠ y in 𝓝 (c (γ s₁)), ‖fderiv ℝ B y - fderiv ℝ A (c (γ s₁))‖ < ε := by
      have hb := hBcont.preimage_mem_nhds (Metric.ball_mem_nhds (fderiv ℝ B (c (γ s₁))) hεpos)
      filter_upwards [hb] with y hy
      rwa [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, hBA] at hy
    have h3 : ∀ᶠ y in 𝓝 (c (γ s₁)), ‖fderiv ℝ Γ y - fderiv ℝ Γ (c (γ s₁))‖ < ε := by
      have hb := hΓcont.preimage_mem_nhds (Metric.ball_mem_nhds (fderiv ℝ Γ (c (γ s₁))) hεpos)
      filter_upwards [hb] with y hy
      rwa [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hy
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
    exact ⟨hy1, hy2, hy3⟩
  obtain ⟨r₁, hr₁pos, hr₁sub⟩ := Metric.mem_nhds_iff.mp hnhds
  obtain ⟨r₂, hr₂pos, hr₂sub⟩ := Metric.isOpen_iff.mp c.open_target (c (γ s₁)) hy₁t
  set r : ℝ := min r₁ r₂ with hrdef
  have hrpos : 0 < r := lt_min hr₁pos hr₂pos
  have hgood : ∀ y ∈ Metric.ball (c (γ s₁)) r, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ ν : EuclideanSpace ℝ (Fin n),
      fderiv ℝ Γ y ν = 0 → (t • fderiv ℝ A y + (1 - t) • fderiv ℝ B y) ν = 0 → ν = 0 := by
    intro y hy t ht ν hv1 hv2
    have hy1 : y ∈ Metric.ball (c (γ s₁)) r₁ := by
      rw [Metric.mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy (min_le_left _ _)
    obtain ⟨hdA, hdB, hdΓ⟩ := hr₁sub hy1
    exact hεprop (fderiv ℝ A y) (fderiv ℝ B y) (fderiv ℝ Γ y) hdA hdB hdΓ t ht ν hv1 hv2
  -- the corresponding neighbourhood of `s₁`
  have hγc : ContinuousAt γ s₁ := hγ.continuous.continuousAt
  have hcc : ContinuousAt (fun s : ℝ => c (γ s)) s₁ := (c.continuousAt hcsrc).comp hγc
  have hV : {s : ℝ | γ s ∈ c.source ∧ c (γ s) ∈ Metric.ball (c (γ s₁)) r} ∈ 𝓝 s₁ := by
    have h1 : γ ⁻¹' c.source ∈ 𝓝 s₁ := hγc.preimage_mem_nhds (c.open_source.mem_nhds hcsrc)
    have h2 : (fun s : ℝ => c (γ s)) ⁻¹' Metric.ball (c (γ s₁)) r ∈ 𝓝 s₁ :=
      hcc.preimage_mem_nhds (Metric.ball_mem_nhds _ hrpos)
    filter_upwards [h1, h2] with s hs1 hs2
    exact ⟨hs1, hs2⟩
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨ρ, hρpos, ?_⟩
  intro χ hχ hχI s hs
  obtain ⟨hsrcc, hsball⟩ := hρsub (by rwa [Metric.mem_ball, Real.dist_eq])
  -- smoothness of the blended map
  have hψsm : ContMDiff (MC n) (MC (n - 1)) smoothOrder
      (fun x : M => χ (g x) • G₁ x + (1 - χ (g x)) • G₂ x) := by
    intro x
    have h1 : ContMDiffAt (MC n) MCreal smoothOrder (fun x : M => χ (g x)) x :=
      ((contMDiff_iff_contDiff.mpr hχ).contMDiffAt (x := g x)).comp x hg.contMDiffAt
    have h2 : ContMDiffAt (MC n) MCreal smoothOrder (fun x : M => 1 - χ (g x)) x :=
      contMDiffAt_const.sub h1
    exact (h1.smul hG₁.contMDiffAt).add (h2.smul hG₂.contMDiffAt)
  -- transversality of the blend
  intro v hv1 hv2
  have hyt : c (γ s) ∈ c.target := c.map_source hsrcc
  have hsymm : c.symm (c (γ s)) = γ s := c.left_inv hsrcc
  -- the manifold derivatives at `γ s`, with concrete types
  let Se : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s))
  let Ce : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (MC n) (MC n) (c : M → EuclideanSpace ℝ (Fin n)) (γ s)
  let T₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) G₁ (γ s)
  let T₂ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) G₂ (γ s)
  let Mψ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1))
      (fun x : M => χ (g x) • G₁ x + (1 - χ (g x)) • G₂ x) (γ s)
  let Lg : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := mfderiv (MC n) MCreal g (γ s)
  have hSeCe : Se.comp Ce = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) :=
    hmd.symm_comp_deriv hsrcc
  have hAder' : fderiv ℝ A (c (γ s)) = T₁.comp Se := by
    have h := (hasFDerivAt_coord (n := n) hG₁ hcm hyt).fderiv
    rw [hsymm] at h
    rw [hAdef]
    exact h
  have hBder' : fderiv ℝ B (c (γ s)) = T₂.comp Se := by
    have h := (hasFDerivAt_coord (n := n) hG₂ hcm hyt).fderiv
    rw [hsymm] at h
    rw [hBdef]
    exact h
  have hΓder' : fderiv ℝ Γ (c (γ s)) = Lg.comp Se := by
    have h := (hasFDerivAt_coord (n := n) hg hcm hyt).fderiv
    rw [hsymm] at h
    rw [hΓdef]
    exact h
  have hψder' : fderiv ℝ (fun y' => (fun x : M => χ (g x) • G₁ x + (1 - χ (g x)) • G₂ x)
        (c.symm y')) (c (γ s)) = Mψ.comp Se := by
    have h := (hasFDerivAt_coord (n := n) hψsm hcm hyt).fderiv
    rw [hsymm] at h
    exact h
  have hprod : fderiv ℝ (fun y' => χ (g (c.symm y')) • G₁ (c.symm y')
        + (1 - χ (g (c.symm y'))) • G₂ (c.symm y')) (c (γ s))
      = χ (g (γ s)) • fderiv ℝ A (c (γ s)) + (1 - χ (g (γ s))) • fderiv ℝ B (c (γ s)) := by
    have h := fderiv_blend_coord (n := n) hχ hg hG₁ hG₂ hcm hyt
      (by rw [hsymm]; exact hv₁ s) (by rw [hsymm]; exact hv₂ s)
    rw [h, hsymm]
  -- the vector in coordinates
  let δ : EuclideanSpace ℝ (Fin n) := Ce v
  have hDs : Se δ = v := by
    have h1 := congrArg
      (fun (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) => L v) hSeCe
    simpa [δ, ContinuousLinearMap.comp_apply] using h1
  have hΓ0 : fderiv ℝ Γ (c (γ s)) δ = 0 := by
    rw [hΓder']
    change Lg (Se δ) = 0
    rw [hDs]
    exact hv2
  have hZ0 : (χ (g (γ s)) • fderiv ℝ A (c (γ s))
      + (1 - χ (g (γ s))) • fderiv ℝ B (c (γ s))) δ = 0 := by
    rw [← hprod]
    have hbridge : (fun y' => χ (g (c.symm y')) • G₁ (c.symm y')
          + (1 - χ (g (c.symm y'))) • G₂ (c.symm y'))
        = (fun y' => (fun x : M => χ (g x) • G₁ x + (1 - χ (g x)) • G₂ x) (c.symm y')) := by
      funext y'; rfl
    rw [hbridge, hψder']
    change Mψ (Se δ) = 0
    rw [hDs]
    exact hv1
  have hδ0 : δ = 0 :=
    hgood (c (γ s)) hsball (χ (g (γ s))) (hχI (g (γ s))) δ hΓ0 hZ0
  calc v = Se δ := hDs.symm
    _ = Se 0 := by rw [hδ0]
    _ = 0 := map_zero _

end

end Work.Noncompact.CompressionTube
