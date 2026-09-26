import Mathlib

/-!
# The zero set of a `C¹` function near a regular zero is the graph of a continuous function

Let `f : ℝ × ℝ → ℝ` be `C¹` with `f 0 = 0` and `(fderiv ℝ f 0) (1, 0) > 0`.  Then, on a small
rectangle `[-Rx, Rx] × [-Ry, Ry]`, the zero set of `f` is the graph of a continuous function `ψ`
of the second variable,
`{f = 0} = {(ψ y, y)}`, and `f (·, y)` changes sign across `ψ y`:
`f (x, y) ≤ 0 ↔ x ≤ ψ y`.

The proof is elementary: `∂f/∂x > 0` on the rectangle (by continuity of the derivative at the
origin), so every slice `x ↦ f (x, y)` is strictly increasing and expanding with a uniform constant
`c > 0`.  The intermediate value theorem on the slice (using `|f (0, y)| < c · Rx`) gives an
existence of a zero, strict monotonicity gives uniqueness, and the expanding inequality gives the
continuity of the root as a function of `y`.

The main theorem `exists_root_pair` applies this to a pair of functions with the same derivative at
the origin.
-/

namespace Work.Smooth.BoxGeneric.LocalArc

open Set

/-! ### Derivative of a slice -/

/-- The partial derivative of `f` in the first variable, computed as the derivative of the slice
`x ↦ f (x, y)`. -/
private lemma deriv_slice {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (x y : ℝ) :
    deriv (fun t : ℝ => f (t, y)) x = (fderiv ℝ f (x, y)) (1, 0) := by
  have h1 : HasFDerivAt (fun t : ℝ => (t, y)) (ContinuousLinearMap.inl ℝ ℝ ℝ) x :=
    hasFDerivAt_prodMk_left x y
  have h2 : HasFDerivAt f (fderiv ℝ f (x, y)) (x, y) :=
    (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have h3 : HasFDerivAt (fun t : ℝ => f (t, y))
      ((fderiv ℝ f (x, y)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) x := h2.comp x h1
  rw [h3.hasDerivAt.deriv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

/-! ### Monotonicity and expansion of a slice -/

/-- If `∂f/∂x ≥ c` on the rectangle then each slice `x ↦ f (x, y)` grows at least as fast as
`c · x`. -/
private lemma slice_expanding_le {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {Rx y c : ℝ}
    (hderiv : ∀ t : ℝ, |t| ≤ Rx → c ≤ (fderiv ℝ f (t, y)) (1, 0)) :
    ∀ t₁ t₂ : ℝ, |t₁| ≤ Rx → |t₂| ≤ Rx → t₁ ≤ t₂ →
      c * (t₂ - t₁) ≤ f (t₂, y) - f (t₁, y) := by
  intro t₁ t₂ ht₁ ht₂ hlt
  have hD : Convex ℝ (Icc (-Rx) Rx) := convex_Icc _ _
  have hcont : ContinuousOn (fun t : ℝ => f (t, y)) (Icc (-Rx) Rx) :=
    (hf.continuous.comp (by fun_prop)).continuousOn
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => f (t, y)) (interior (Icc (-Rx) Rx)) :=
    (((hf.differentiable (by norm_num)).comp
      (by fun_prop : Differentiable ℝ (fun t : ℝ => (t, y))))).differentiableOn
  have hderiv' : ∀ t ∈ interior (Icc (-Rx) Rx), c ≤ deriv (fun t : ℝ => f (t, y)) t := by
    intro t ht
    rw [deriv_slice hf]
    apply hderiv
    rw [interior_Icc] at ht
    exact le_of_lt (abs_lt.mpr ht)
  have := hD.mul_sub_le_image_sub_of_le_deriv hcont hdiff hderiv' t₁
    (Set.mem_Icc.mpr (abs_le.mp ht₁)) t₂ (Set.mem_Icc.mpr (abs_le.mp ht₂)) hlt
  simpa using this

/-- Strict version of `slice_expanding_le`. -/
private lemma slice_expanding {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {Rx y c : ℝ}
    (hderiv : ∀ t : ℝ, |t| ≤ Rx → c < (fderiv ℝ f (t, y)) (1, 0)) :
    ∀ t₁ t₂ : ℝ, |t₁| ≤ Rx → |t₂| ≤ Rx → t₁ < t₂ →
      c * (t₂ - t₁) < f (t₂, y) - f (t₁, y) := by
  intro t₁ t₂ ht₁ ht₂ hlt
  have hD : Convex ℝ (Icc (-Rx) Rx) := convex_Icc _ _
  have hcont : ContinuousOn (fun t : ℝ => f (t, y)) (Icc (-Rx) Rx) :=
    (hf.continuous.comp (by fun_prop)).continuousOn
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => f (t, y)) (interior (Icc (-Rx) Rx)) :=
    (((hf.differentiable (by norm_num)).comp
      (by fun_prop : Differentiable ℝ (fun t : ℝ => (t, y))))).differentiableOn
  have hderiv' : ∀ t ∈ interior (Icc (-Rx) Rx), c < deriv (fun t : ℝ => f (t, y)) t := by
    intro t ht
    rw [deriv_slice hf]
    apply hderiv
    rw [interior_Icc] at ht
    exact le_of_lt (abs_lt.mpr ht)
  have := hD.mul_sub_lt_image_sub_of_lt_deriv hcont hdiff hderiv' t₁
    (Set.mem_Icc.mpr (abs_le.mp ht₁)) t₂ (Set.mem_Icc.mpr (abs_le.mp ht₂)) hlt
  simpa using this

/-- The slice `x ↦ f (x, y)` is expanding: `c |t₂ - t₁| ≤ |f (t₂, y) - f (t₁, y)|`. -/
private lemma slice_dist_bound {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {Rx y c : ℝ}
    (hderiv : ∀ t : ℝ, |t| ≤ Rx → c ≤ (fderiv ℝ f (t, y)) (1, 0)) :
    ∀ t₁ t₂ : ℝ, |t₁| ≤ Rx → |t₂| ≤ Rx →
      c * |t₂ - t₁| ≤ |f (t₂, y) - f (t₁, y)| := by
  intro t₁ t₂ ht₁ ht₂
  have hexp := slice_expanding_le hf hderiv
  rcases le_total t₁ t₂ with hle | hle
  · have h := hexp t₁ t₂ ht₁ ht₂ hle
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    linarith [le_abs_self (f (t₂, y) - f (t₁, y))]
  · have h := hexp t₂ t₁ ht₂ ht₁ hle
    have habs : |t₂ - t₁| = t₁ - t₂ := by
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]; ring
    rw [habs]
    have h'' : f (t₁, y) - f (t₂, y) ≤ |f (t₂, y) - f (t₁, y)| := by
      rw [abs_sub_comm]; exact le_abs_self _
    linarith

/-! ### The zero set on a rectangle is a graph -/

/-- **The graph of the zero set.**  Given a uniform lower bound `c > 0` for `∂f/∂x` on the
rectangle `[-Rx, Rx] × [-Ry, Ry]` and the smallness condition `|f (0, y)| < c · Rx` there, the zero
set of `f` on the rectangle is the graph of a continuous function `ψ` of the second variable, and
`f (·, y)` changes sign across `ψ y`. -/
private theorem root_graph {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0)
    {Rx Ry c : ℝ} (hRx : 0 < Rx) (hRy : 0 < Ry) (hc : 0 < c)
    (hderiv : ∀ x y, |x| ≤ Rx → |y| ≤ Ry → c < (fderiv ℝ f (x, y)) (1, 0))
    (hsmall : ∀ y, |y| ≤ Ry → |f (0, y)| < c * Rx) :
    ∃ ψ : ℝ → ℝ, ψ 0 = 0 ∧ ContinuousOn ψ (Ioo (-Ry) Ry) ∧
      (∀ y, |y| ≤ Ry → |ψ y| ≤ Rx ∧ f (ψ y, y) = 0) ∧
      (∀ x y, |x| ≤ Rx → |y| ≤ Ry → (f (x, y) ≤ 0 ↔ x ≤ ψ y)) ∧
      (∀ x y, |x| ≤ Rx → |y| ≤ Ry → (f (x, y) = 0 ↔ x = ψ y)) := by
  -- Existence of a zero in the open rectangle for every `|y| ≤ Ry`.
  have hroot : ∀ y : ℝ, |y| ≤ Ry → ∃ x : ℝ, x ∈ Ioo (-Rx) Rx ∧ f (x, y) = 0 := by
    intro y hy
    have hderiv_y : ∀ t : ℝ, |t| ≤ Rx → c < (fderiv ℝ f (t, y)) (1, 0) :=
      fun t ht => hderiv t y ht hy
    have hexp := slice_expanding hf hderiv_y
    have hpos : 0 < f (Rx, y) := by
      have h1 := hexp 0 Rx (by simpa using hRx.le) (by rw [abs_of_pos hRx]) hRx
      have h2 := hsmall y hy
      have h3 := neg_abs_le (f (0, y))
      linarith
    have hneg : f (-Rx, y) < 0 := by
      have h1 := hexp (-Rx) 0 (by rw [abs_neg, abs_of_pos hRx]) (by simpa using hRx.le)
        (by linarith)
      have h2 := hsmall y hy
      have h3 := le_abs_self (f (0, y))
      linarith
    have hcont : ContinuousOn (fun t : ℝ => f (t, y)) (Icc (-Rx) Rx) :=
      (hf.continuous.comp (by fun_prop)).continuousOn
    have hmem : (0:ℝ) ∈ Ioo ((fun t : ℝ => f (t, y)) (-Rx)) ((fun t : ℝ => f (t, y)) Rx) := by
      show (0:ℝ) ∈ Ioo (f (-Rx, y)) (f (Rx, y))
      exact Set.mem_Ioo.mpr ⟨hneg, hpos⟩
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo (show -Rx ≤ Rx by linarith) hcont hmem
    exact ⟨x, hx, hfx⟩
  -- The root as a function of `y`.
  let ψ : ℝ → ℝ := fun y => if h : |y| ≤ Ry then Classical.choose (hroot y h) else 0
  have hψ_apply : ∀ y (h : |y| ≤ Ry), ψ y = Classical.choose (hroot y h) := by
    intro y h
    show (if h' : |y| ≤ Ry then Classical.choose (hroot y h') else 0) = _
    rw [dif_pos h]
  have hψ_root : ∀ y (h : |y| ≤ Ry), (ψ y ∈ Ioo (-Rx) Rx) ∧ f (ψ y, y) = 0 := by
    intro y h
    rw [hψ_apply y h]
    exact Classical.choose_spec (hroot y h)
  -- Strict monotonicity of every slice.
  have hmono : ∀ y, |y| ≤ Ry → StrictMonoOn (fun t : ℝ => f (t, y)) (Icc (-Rx) Rx) := by
    intro y hy t₁ ht₁ t₂ ht₂ hlt
    have hderiv_y : ∀ t : ℝ, |t| ≤ Rx → c < (fderiv ℝ f (t, y)) (1, 0) :=
      fun t ht => hderiv t y ht hy
    have h := slice_expanding hf hderiv_y t₁ t₂ (abs_le.mpr (Set.mem_Icc.mp ht₁))
      (abs_le.mpr (Set.mem_Icc.mp ht₂)) hlt
    show f (t₁, y) < f (t₂, y)
    have hmul : 0 < c * (t₂ - t₁) := mul_pos hc (sub_pos.mpr hlt)
    linarith
  -- Continuity of the root.
  have hψcontAt : ∀ y₀ ∈ Ioo (-Ry) Ry, ContinuousAt ψ y₀ := by
    intro y₀ hy₀
    have hy₀abs : |y₀| < Ry := abs_lt.mpr ⟨hy₀.1, hy₀.2⟩
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hδ₁ : 0 < Ry - |y₀| := sub_pos.mpr hy₀abs
    have hfcont : ContinuousAt f (ψ y₀, y₀) := hf.continuous.continuousAt
    rw [Metric.continuousAt_iff] at hfcont
    obtain ⟨η, hηpos, hηspec⟩ := hfcont (c * ε) (by positivity)
    refine ⟨min (Ry - |y₀|) η, lt_min hδ₁ hηpos, ?_⟩
    intro y hy
    have hy₁ : dist y y₀ < Ry - |y₀| := lt_of_lt_of_le hy (min_le_left _ _)
    have hy₂ : dist y y₀ < η := lt_of_lt_of_le hy (min_le_right _ _)
    rw [Real.dist_eq] at hy₁ hy₂
    have hyb : |y| < Ry := by
      have h : |y| ≤ |y₀| + |y - y₀| := by
        have h' : y₀ + (y - y₀) = y := by ring
        simpa [h'] using abs_add_le y₀ (y - y₀)
      linarith
    obtain ⟨hmem_y, hval_y⟩ := hψ_root y hyb.le
    obtain ⟨hmem_0, hval_0⟩ := hψ_root y₀ hy₀abs.le
    have hderiv_y : ∀ t : ℝ, |t| ≤ Rx → c ≤ (fderiv ℝ f (t, y)) (1, 0) :=
      fun t ht => (hderiv t y ht hyb.le).le
    have hbnd := slice_dist_bound hf hderiv_y (ψ y₀) (ψ y)
      (abs_le.mpr ⟨hmem_0.1.le, hmem_0.2.le⟩) (abs_le.mpr ⟨hmem_y.1.le, hmem_y.2.le⟩)
    have hdist : dist ((ψ y₀, y) : ℝ × ℝ) (ψ y₀, y₀) < η := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_right (abs_nonneg _)]
      exact hy₂
    have hkey : |f (ψ y₀, y) - f (ψ y₀, y₀)| < c * ε := by
      have hh := hηspec hdist
      rwa [Real.dist_eq] at hh
    have hfin : c * |ψ y - ψ y₀| < c * ε := by
      calc c * |ψ y - ψ y₀| ≤ |f (ψ y, y) - f (ψ y₀, y)| := hbnd
        _ = |f (ψ y₀, y)| := by rw [hval_y, zero_sub, abs_neg]
        _ = |f (ψ y₀, y) - f (ψ y₀, y₀)| := by rw [hval_0, sub_zero]
        _ < c * ε := hkey
    rw [Real.dist_eq]
    exact lt_of_mul_lt_mul_left hfin hc.le
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_⟩
  · -- `ψ 0 = 0`
    have h0 : |(0:ℝ)| ≤ Ry := by rw [abs_zero]; exact hRy.le
    obtain ⟨hmem, hval⟩ := hψ_root 0 h0
    have hmem' : ψ 0 ∈ Icc (-Rx) Rx := Ioo_subset_Icc_self hmem
    have h0mem : (0:ℝ) ∈ Icc (-Rx) Rx := Set.mem_Icc.mpr ⟨by linarith, hRx.le⟩
    have heq : (fun t : ℝ => f (t, 0)) (ψ 0) = (fun t : ℝ => f (t, 0)) 0 := by
      show f (ψ 0, 0) = f (0, 0)
      rw [hval]
      exact hf0.symm
    exact (hmono 0 h0).injOn hmem' h0mem heq
  · intro y₀ hy₀
    exact (hψcontAt y₀ hy₀).continuousWithinAt
  · intro y hy
    obtain ⟨hmem, hval⟩ := hψ_root y hy
    exact ⟨le_of_lt (abs_lt.mpr ⟨hmem.1, hmem.2⟩), hval⟩
  · -- sign of `f`
    intro x y hx hy
    obtain ⟨hmem, hval⟩ := hψ_root y hy
    have hmem' : ψ y ∈ Icc (-Rx) Rx := Ioo_subset_Icc_self hmem
    have hxmem : x ∈ Icc (-Rx) Rx := Set.mem_Icc.mpr (abs_le.mp hx)
    have hm := hmono y hy
    constructor
    · intro hfx
      by_contra hcon
      rw [not_le] at hcon
      have hlt : f (ψ y, y) < f (x, y) := hm hmem' hxmem hcon
      rw [hval] at hlt
      linarith
    · intro hxy
      rcases lt_or_eq_of_le hxy with hlt | heq
      · have hlt' : f (x, y) < f (ψ y, y) := hm hxmem hmem' hlt
        rw [hval] at hlt'
        linarith
      · rw [heq, hval]
  · -- vanishing of `f`
    intro x y hx hy
    obtain ⟨hmem, hval⟩ := hψ_root y hy
    have hmem' : ψ y ∈ Icc (-Rx) Rx := Ioo_subset_Icc_self hmem
    have hxmem : x ∈ Icc (-Rx) Rx := Set.mem_Icc.mpr (abs_le.mp hx)
    have hm := hmono y hy
    constructor
    · intro hfx
      apply hm.injOn hxmem hmem'
      show f (x, y) = f (ψ y, y)
      rw [hfx, hval]
    · intro hxy
      rw [hxy, hval]

/-! ### Choosing the rectangle for one function -/

/-- For a single `C¹` function with `f 0 = 0` and `∂f/∂x (0) > 0`: there is a rectangle around
the origin on which the zero set is a graph over the second coordinate. -/
private theorem exists_root_single {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0)
    (ha : 0 < (fderiv ℝ f 0) (1, 0)) :
    ∃ Rx Ry : ℝ, 0 < Rx ∧ 0 < Ry ∧ ∃ ψ : ℝ → ℝ, ψ 0 = 0 ∧
      ContinuousOn ψ (Ioo (-Ry) Ry) ∧
      (∀ y, |y| ≤ Ry → |ψ y| ≤ Rx ∧ f (ψ y, y) = 0) ∧
      (∀ x y, |x| ≤ Rx → |y| ≤ Ry → (f (x, y) ≤ 0 ↔ x ≤ ψ y)) ∧
      (∀ x y, |x| ≤ Rx → |y| ≤ Ry → (f (x, y) = 0 ↔ x = ψ y)) := by
  set P : ℝ × ℝ → ℝ := fun z => (fderiv ℝ f z) (1, 0) with hP_def
  have hPcont : Continuous P := by
    rw [hP_def]
    exact (hf.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)
  set c : ℝ := (fderiv ℝ f 0) (1, 0) / 2 with hc_def
  have hc : 0 < c := by rw [hc_def]; linarith
  have hP0 : P 0 = 2 * c := by rw [hP_def, hc_def]; ring
  have hPc0 : ContinuousAt P 0 := hPcont.continuousAt
  rw [Metric.continuousAt_iff] at hPc0
  obtain ⟨δ₁, hδ₁pos, hδ₁spec⟩ := hPc0 c hc
  have hPgt : ∀ z : ℝ × ℝ, dist z 0 < δ₁ → c < P z := by
    intro z hz
    have h := hδ₁spec hz
    rw [Real.dist_eq, hP0] at h
    linarith [neg_abs_le (P z - 2 * c)]
  set Rx : ℝ := δ₁ / 2 with hRx_def
  have hRxpos : 0 < Rx := by rw [hRx_def]; linarith
  have hsmallcont : ContinuousAt (fun y : ℝ => f (0, y)) 0 :=
    (hf.continuous.comp (by fun_prop)).continuousAt
  rw [Metric.continuousAt_iff] at hsmallcont
  obtain ⟨η, hηpos, hηspec⟩ := hsmallcont (c * Rx) (mul_pos hc hRxpos)
  set Ry : ℝ := min Rx (η / 2) with hRy_def
  have hRypos : 0 < Ry := by rw [hRy_def]; exact lt_min hRxpos (by linarith)
  have hsmall : ∀ y, |y| ≤ Ry → |f (0, y)| < c * Rx := by
    intro y hy
    have hfy : dist y 0 < η := by
      rw [Real.dist_eq, sub_zero]
      have hy' : |y| ≤ Ry := hy
      rw [hRy_def] at hy'
      linarith [min_le_right Rx (η / 2)]
    have h := hηspec hfy
    rw [Real.dist_eq] at h
    have hf00 : f (0, 0) = 0 := hf0
    rw [hf00, sub_zero] at h
    exact h
  have hbox : ∀ x y, |x| ≤ Rx → |y| ≤ Ry → c < (fderiv ℝ f (x, y)) (1, 0) := by
    intro x y hx hy
    have hnorm : dist ((x, y) : ℝ × ℝ) 0 < δ₁ := by
      rw [dist_eq_norm, sub_zero, Prod.norm_def]
      simp only [Real.norm_eq_abs]
      have hxδ : |x| < δ₁ := by
        have hxR : |x| ≤ Rx := hx
        rw [hRx_def] at hxR; linarith
      have hyδ : |y| < δ₁ := by
        have hyR : |y| ≤ Ry := hy
        rw [hRy_def] at hyR
        linarith [min_le_left Rx (η / 2)]
      exact max_lt hxδ hyδ
    have h := hPgt (x, y) hnorm
    rw [hP_def] at h
    exact h
  obtain ⟨ψ, hψ0, hψcont, hψroot, hψsign, hψzero⟩ :=
    root_graph hf hf0 hRxpos hRypos hc hbox hsmall
  exact ⟨Rx, Ry, hRxpos, hRypos, ψ, hψ0, hψcont, hψroot, hψsign, hψzero⟩

/-! ### Shrinking the interval of definition -/

/-- A function continuous at the origin with value `0` there is bounded by `R` on a symmetric
neighbourhood of the origin. -/
private lemma exists_abs_le_of_continuousAt_zero {ψ : ℝ → ℝ} {R : ℝ}
    (hcont : ContinuousAt ψ 0) (h0 : ψ 0 = 0) (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y| ≤ δ → |ψ y| ≤ R := by
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ₀, hδ₀pos, hδ₀spec⟩ := hcont R hR
  refine ⟨δ₀ / 2, by linarith, ?_⟩
  intro y hy
  have hy' : dist y 0 < δ₀ := by
    rw [Real.dist_eq, sub_zero]; linarith
  have h := hδ₀spec hy'
  rw [Real.dist_eq, h0, sub_zero] at h
  exact h.le

/-! ### The main theorem -/

theorem exists_root_pair {F G : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (hF0 : F 0 = 0) (hG0 : G 0 = 0) (htang : fderiv ℝ F 0 = fderiv ℝ G 0)
    (ha : 0 < (fderiv ℝ F 0) (1, 0)) :
    ∃ Rx Ry : ℝ, 0 < Rx ∧ 0 < Ry ∧ ∃ ψ φ : ℝ → ℝ,
      ψ 0 = 0 ∧ φ 0 = 0 ∧
      ContinuousOn ψ (Set.Ioo (-Ry) Ry) ∧ ContinuousOn φ (Set.Ioo (-Ry) Ry) ∧
      (∀ y : ℝ, |y| ≤ Ry → |ψ y| ≤ Rx ∧ |φ y| ≤ Rx ∧ F (ψ y, y) = 0 ∧ G (φ y, y) = 0) ∧
      (∀ x y : ℝ, |x| ≤ Rx → |y| ≤ Ry → (F (x, y) ≤ 0 ↔ x ≤ ψ y) ∧ (G (x, y) ≤ 0 ↔ x ≤ φ y)) ∧
      (∀ x y : ℝ, |x| ≤ Rx → |y| ≤ Ry → (F (x, y) = 0 ↔ x = ψ y) ∧ (G (x, y) = 0 ↔ x = φ y)) := by
  obtain ⟨RxF, RyF, hRxFpos, hRyFpos, ψ, hψ0, hψcont, hψroot, hψsign, hψzero⟩ :=
    exists_root_single hF hF0 ha
  have haG : 0 < (fderiv ℝ G 0) (1, 0) := by rw [← htang]; exact ha
  obtain ⟨RxG, RyG, hRxGpos, hRyGpos, φ, hφ0, hφcont, hφroot, hφsign, hφzero⟩ :=
    exists_root_single hG hG0 haG
  -- a common half-width in the first coordinate
  set Rx : ℝ := min RxF RxG with hRx_def
  have hRxpos : 0 < Rx := by rw [hRx_def]; exact lt_min hRxFpos hRxGpos
  have hRxleF : Rx ≤ RxF := by rw [hRx_def]; exact min_le_left _ _
  have hRxleG : Rx ≤ RxG := by rw [hRx_def]; exact min_le_right _ _
  -- shrink the second coordinate so that the roots stay in `[-Rx, Rx]`
  have hψcontAt0 : ContinuousAt ψ 0 :=
    hψcont.continuousAt (isOpen_Ioo.mem_nhds (by
      rw [Set.mem_Ioo]; exact ⟨by linarith, hRyFpos⟩))
  have hφcontAt0 : ContinuousAt φ 0 :=
    hφcont.continuousAt (isOpen_Ioo.mem_nhds (by
      rw [Set.mem_Ioo]; exact ⟨by linarith, hRyGpos⟩))
  obtain ⟨δψ, hδψpos, hδψ⟩ := exists_abs_le_of_continuousAt_zero hψcontAt0 hψ0 hRxpos
  obtain ⟨δφ, hδφpos, hδφ⟩ := exists_abs_le_of_continuousAt_zero hφcontAt0 hφ0 hRxpos
  set Ry : ℝ := min (min δψ δφ) (min RyF RyG) with hRy_def
  have hRypos : 0 < Ry := by
    rw [hRy_def]; exact lt_min (lt_min hδψpos hδφpos) (lt_min hRyFpos hRyGpos)
  have hRyleF : Ry ≤ RyF := by
    rw [hRy_def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hRyleG : Ry ≤ RyG := by
    rw [hRy_def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hRyleδψ : Ry ≤ δψ := by
    rw [hRy_def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hRyleδφ : Ry ≤ δφ := by
    rw [hRy_def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  refine ⟨Rx, Ry, hRxpos, hRypos, ψ, φ, hψ0, hφ0, ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity of `ψ` on the smaller interval
    refine hψcont.mono ?_
    intro y hy
    rw [Set.mem_Ioo] at hy ⊢
    exact ⟨by linarith [hy.1, hRyleF], by linarith [hy.2, hRyleF]⟩
  · refine hφcont.mono ?_
    intro y hy
    rw [Set.mem_Ioo] at hy ⊢
    exact ⟨by linarith [hy.1, hRyleG], by linarith [hy.2, hRyleG]⟩
  · intro y hy
    obtain ⟨hψa, hψb⟩ := hψroot y (le_trans hy hRyleF)
    obtain ⟨hφa, hφb⟩ := hφroot y (le_trans hy hRyleG)
    exact ⟨hδψ y (le_trans hy hRyleδψ), hδφ y (le_trans hy hRyleδφ), hψb, hφb⟩
  · intro x y hx hy
    exact ⟨hψsign x y (le_trans hx hRxleF) (le_trans hy hRyleF),
      hφsign x y (le_trans hx hRxleG) (le_trans hy hRyleG)⟩
  · intro x y hx hy
    exact ⟨hψzero x y (le_trans hx hRxleF) (le_trans hy hRyleF),
      hφzero x y (le_trans hx hRxleG) (le_trans hy hRyleG)⟩

end Work.Smooth.BoxGeneric.LocalArc
