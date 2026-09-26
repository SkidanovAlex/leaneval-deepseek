import Mathlib
import Submission.Work.Smooth.BoxGeneric.LocalArc.exists_root_pair
import Submission.Work.Smooth.BoxGeneric.LocalArc.local_arc_of_max_of_tangential

/-!
# The maximum of a finite family of `C¹` functions tangent to `x` near the origin

Let `f : ι → ℝ × ℝ → ℝ` be a finite nonempty family of `C¹` functions with `f i 0 = 0` and
`fderiv ℝ (f i) 0 = ContinuousLinearMap.fst ℝ ℝ ℝ` (that is, `∂ₓ f i (0) = 1` and
`∂_y f i (0) = 0`) for every `i`.  Then near the origin the zero set of the maximum
`M = sup'_i f i` is the graph `x = φ y` of a continuous function whose slope is bounded by `1/2`:

`Work.Drive.Mono.family_max_graph_slope` produces a rectangle `[-R₁, R₁] × [-R₂, R₂]` and a
continuous `φ : ℝ → ℝ` with `φ 0 = 0`, `|φ y| ≤ |y| / 2` for `|y| ≤ R₂`, such that on the
rectangle

* `M (x, y) ≤ 0 ↔ x ≤ φ y`, and
* `M (x, y) = 0 ↔ x = φ y`.

The proof is elementary.  Writing `e i = f i - fst`, each `e i` is `C¹` with `e i 0 = 0` and
`fderiv ℝ (e i) 0 = 0`, so `e i (z) = o(‖z‖)` uniformly in the (finite) family; on a small box the
slices `x ↦ f i (x, y)` are `1/2`-expanding (because `∂ₓ f i = 1` at the origin and the family is
finite), and hence so is the slice of the maximum `M`.  A maximum of an expanding family crosses
zero exactly once on the box (intermediate values + strict monotonicity), which yields `φ`; the
`o(‖z‖)` bound evaluated at `x = ±|y|/2` gives the slope bound, and the uniform continuity of `M`
on compact rectangles gives the continuity of `φ`.
-/

namespace Work.Drive.Mono

open Filter Set
open scoped Topology

/-! ### A slice of a `C¹` function and its derivative in the first variable -/

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

/-! ### Expanding slices -/

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
  exact hD.mul_sub_le_image_sub_of_le_deriv hcont hdiff hderiv' t₁
    (Set.mem_Icc.mpr (abs_le.mp ht₁)) t₂ (Set.mem_Icc.mpr (abs_le.mp ht₂)) hlt

/-! ### The `o(‖z‖)` bound at a zero of the derivative -/

private lemma abs_le_mul_norm_of_fderiv_eq_zero {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hg0 : g 0 = 0) (hdg : fderiv ℝ g 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ × ℝ, ‖z‖ ≤ δ → |g z| ≤ ε * ‖z‖ := by
  have hfd : HasFDerivAt g (0 : (ℝ × ℝ) →L[ℝ] ℝ) 0 := by
    have h : HasFDerivAt g (fderiv ℝ g 0) 0 := by
      exact (hg.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    rwa [hdg] at h
  have hlo : (fun z : ℝ × ℝ => g z) =o[𝓝 (0 : ℝ × ℝ)] (fun z : ℝ × ℝ => z) := by
    have h := hfd.isLittleO
    simpa [hg0] using h
  have hev : ∀ᶠ z : ℝ × ℝ in 𝓝 (0 : ℝ × ℝ), ‖g z‖ ≤ ε * ‖z‖ := hlo.def hε
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδspec⟩ := hev
  refine ⟨δ / 2, by linarith, fun z hz => ?_⟩
  have hzd : dist z (0 : ℝ × ℝ) < δ := by
    rw [dist_zero_right]; linarith
  have := hδspec hzd
  rwa [Real.norm_eq_abs] at this

/-! ### Two elementary algebraic lemmas -/

private lemma sup'_add_const {γ : Type*} {s : Finset γ} (hs : s.Nonempty) (g : γ → ℝ) (c : ℝ) :
    s.sup' hs (fun i => g i + c) = s.sup' hs g + c := by
  have h1 : s.sup' hs (fun i => g i + c) ≤ s.sup' hs g + c :=
    Finset.sup'_le hs _ fun i hi => by
      have := Finset.le_sup' g hi; linarith
  have h2 : s.sup' hs g + c ≤ s.sup' hs (fun i => g i + c) := by
    have h3 : s.sup' hs g ≤ s.sup' hs (fun i => g i + c) - c :=
      Finset.sup'_le hs g fun i hi => by
        have := Finset.le_sup' (fun i => g i + c) hi; linarith
    linarith
  linarith

private lemma fderiv_sub_fst {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hdg : fderiv ℝ g 0 = ContinuousLinearMap.fst ℝ ℝ ℝ) :
    fderiv ℝ (fun z : ℝ × ℝ => g z - z.1) 0 = 0 := by
  have hg' : HasFDerivAt g (fderiv ℝ g 0) 0 := by
    exact (hg.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (fun z : ℝ × ℝ => z.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) 0 :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have h1 : HasFDerivAt (fun z : ℝ × ℝ => g z - z.1)
      ((fderiv ℝ g 0) - ContinuousLinearMap.fst ℝ ℝ ℝ) 0 := hg'.sub h2
  rw [h1.fderiv, hdg, sub_self]

/-- The maximum of the family, as a function of the plane variable. -/
private def familySup {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun z => Finset.sup' Finset.univ Finset.univ_nonempty (fun i => f i z)

/-! ### Continuity of the graph over a parameter -/

private lemma continuousOn_of_expanding {M : ℝ × ℝ → ℝ} {R c : ℝ} (hMcont : Continuous M)
    (hc : 0 < c)
    (hexp : ∀ x₁ x₂ y : ℝ, |x₁| ≤ R → |x₂| ≤ R → |y| ≤ R → x₁ ≤ x₂ →
      c * (x₂ - x₁) ≤ M (x₂, y) - M (x₁, y))
    {φ : ℝ → ℝ} (hφmem : ∀ y, |y| ≤ R → |φ y| ≤ R)
    (hφ0 : ∀ y, |y| ≤ R → M (φ y, y) = 0) :
    ContinuousOn φ (Ioo (-R) R) := by
  intro y₀ hy₀
  have hy₀abs : |y₀| < R := abs_lt.mpr hy₀
  have key : ∀ ε > 0, ∃ δ > 0, ∀ y : ℝ, dist y y₀ < δ → dist (φ y) (φ y₀) < ε := by
    intro ε hε
    set r : ℝ := (R - |y₀|) / 2 with hrdef
    have hrpos : 0 < r := by rw [hrdef]; linarith
    have hunif : UniformContinuousOn M (Icc (-R) R ×ˢ Icc (y₀ - r) (y₀ + r)) :=
      (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hMcont.continuousOn
    rw [Metric.uniformContinuousOn_iff] at hunif
    obtain ⟨δ, hδpos, hδspec⟩ := hunif (c * ε) (mul_pos hc hε)
    refine ⟨min δ r, lt_min hδpos hrpos, fun y hy => ?_⟩
    have hyd : dist y y₀ < δ := lt_of_lt_of_le hy (min_le_left _ _)
    have hyr : dist y y₀ < r := lt_of_lt_of_le hy (min_le_right _ _)
    have hdiffy : |y - y₀| < r := by rwa [Real.dist_eq] at hyr
    have hyR : |y| ≤ R := by
      have h1 : |y| ≤ |y₀| + |y - y₀| := by
        have h2 : y₀ + (y - y₀) = y := by ring
        calc |y| = |y₀ + (y - y₀)| := by rw [h2]
          _ ≤ |y₀| + |y - y₀| := abs_add_le _ _
      have h4 : |y₀| + r = (R + |y₀|) / 2 := by rw [hrdef]; ring
      linarith
    have hφyR : |φ y| ≤ R := hφmem y hyR
    have hφy₀R : |φ y₀| ≤ R := hφmem y₀ (le_of_lt hy₀abs)
    have hyK : y ∈ Icc (y₀ - r) (y₀ + r) := by
      rw [mem_Icc]
      have h2 := abs_lt.mp hdiffy
      constructor <;> linarith [h2.1, h2.2]
    have hy₀K : y₀ ∈ Icc (y₀ - r) (y₀ + r) := by
      rw [mem_Icc]; constructor <;> linarith
    have hxR : φ y ∈ Icc (-R) R := mem_Icc.mpr ⟨(abs_le.mp hφyR).1, (abs_le.mp hφyR).2⟩
    have hmem1 : ((φ y, y) : ℝ × ℝ) ∈ Icc (-R) R ×ˢ Icc (y₀ - r) (y₀ + r) := ⟨hxR, hyK⟩
    have hmem2 : ((φ y, y₀) : ℝ × ℝ) ∈ Icc (-R) R ×ˢ Icc (y₀ - r) (y₀ + r) := ⟨hxR, hy₀K⟩
    have hdist : dist ((φ y, y) : ℝ × ℝ) (φ y, y₀) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
      exact hyd
    have hbound : |M (φ y, y) - M (φ y, y₀)| < c * ε := by
      have := hδspec _ hmem1 _ hmem2 hdist
      rwa [Real.dist_eq] at this
    have hφy0 : M (φ y, y) = 0 := hφ0 y hyR
    have hφy₀0 : M (φ y₀, y₀) = 0 := hφ0 y₀ (le_of_lt hy₀abs)
    rcases le_total (φ y₀) (φ y) with hle | hle
    · have hex := hexp (φ y₀) (φ y) y₀ hφy₀R hφyR (le_of_lt hy₀abs) hle
      rw [hφy₀0] at hex
      have h2 : M (φ y, y₀) ≤ |M (φ y, y) - M (φ y, y₀)| := by
        rw [hφy0, zero_sub, abs_neg]; exact le_abs_self _
      have : c * (φ y - φ y₀) < c * ε := by linarith
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hle)]
      exact lt_of_mul_lt_mul_left this hc.le
    · have hex := hexp (φ y) (φ y₀) y₀ hφyR hφy₀R (le_of_lt hy₀abs) hle
      rw [hφy₀0] at hex
      have h2 : -M (φ y, y₀) ≤ |M (φ y, y) - M (φ y, y₀)| := by
        rw [hφy0, zero_sub, abs_neg]; exact neg_le_abs _
      have : c * (φ y₀ - φ y) < c * ε := by linarith
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hle)]
      have h3 := lt_of_mul_lt_mul_left this hc.le
      linarith
  exact (Metric.continuousAt_iff.mpr key).continuousWithinAt

/-! ### The main statement -/

theorem family_max_graph_slope {ι : Type*} [Fintype ι] [Nonempty ι]
    {f : ι → ℝ × ℝ → ℝ} (hf : ∀ i, ContDiff ℝ 1 (f i)) (hf0 : ∀ i, f i 0 = 0)
    (hdf : ∀ i, fderiv ℝ (f i) 0 = ContinuousLinearMap.fst ℝ ℝ ℝ) :
    ∃ R₁ R₂ : ℝ, 0 < R₁ ∧ 0 < R₂ ∧ ∃ φ : ℝ → ℝ, φ 0 = 0 ∧
      ContinuousOn φ (Set.Ioo (-R₂) R₂) ∧
      (∀ y : ℝ, |y| ≤ R₂ → |φ y| ≤ |y| / 2) ∧
      (∀ x y : ℝ, |x| ≤ R₁ → |y| ≤ R₂ →
        (Finset.sup' Finset.univ Finset.univ_nonempty (fun i => f i (x, y)) ≤ 0 ↔ x ≤ φ y) ∧
        (Finset.sup' Finset.univ Finset.univ_nonempty (fun i => f i (x, y)) = 0 ↔ x = φ y)) := by
  have hMcont : Continuous (familySup f) := by
    show Continuous (fun z : ℝ × ℝ =>
      Finset.sup' Finset.univ Finset.univ_nonempty (fun i => f i z))
    exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => (hf i).continuous)
  -- *Step 1*: a box on which `∂ₓ f i ≥ 1/2` and `|f i - x| ≤ ‖z‖/4` for every `i`.
  have hmain : ∃ R : ℝ, 0 < R ∧
      (∀ i (z : ℝ × ℝ), ‖z‖ ≤ R → |f i z - z.1| ≤ ‖z‖ / 4) ∧
      (∀ i (z : ℝ × ℝ), ‖z‖ ≤ R → (1/2 : ℝ) ≤ (fderiv ℝ (f i) z) (1, 0)) := by
    have h₁ : ∀ i, ∃ δ : ℝ, 0 < δ ∧
        ∀ z : ℝ × ℝ, ‖z‖ ≤ δ → (1/2 : ℝ) ≤ (fderiv ℝ (f i) z) (1, 0) := by
      intro i
      have hPcont : Continuous (fun z : ℝ × ℝ => (fderiv ℝ (f i) z) (1, 0)) :=
        ((hf i).continuous_fderiv_apply (by norm_num)).comp
          (continuous_id.prodMk continuous_const)
      have hP0 : (fderiv ℝ (f i) 0) (1, 0) = 1 := by rw [hdf i]; simp
      obtain ⟨δ, hδpos, hδspec⟩ :=
        (Metric.continuousAt_iff.mp hPcont.continuousAt) (1 / 2) (by norm_num)
      refine ⟨δ / 2, by linarith, fun z hz => ?_⟩
      have hzd : dist z (0 : ℝ × ℝ) < δ := by rw [dist_zero_right]; linarith
      have h := hδspec hzd
      rw [Real.dist_eq, hP0] at h
      have h2 := neg_abs_le ((fderiv ℝ (f i) z) (1, 0) - 1)
      linarith
    have h₂ : ∀ i, ∃ δ : ℝ, 0 < δ ∧
        ∀ z : ℝ × ℝ, ‖z‖ ≤ δ → |f i z - z.1| ≤ ‖z‖ / 4 := by
      intro i
      have hcd : ContDiff ℝ 1 (fun z : ℝ × ℝ => f i z - z.1) :=
        (hf i).sub (ContinuousLinearMap.contDiff (ContinuousLinearMap.fst ℝ ℝ ℝ))
      have h0' : (fun z : ℝ × ℝ => f i z - z.1) 0 = 0 := by simp [hf0 i]
      have hd' := fderiv_sub_fst (hf i) (hdf i)
      obtain ⟨δ, hδpos, hδspec⟩ :=
        abs_le_mul_norm_of_fderiv_eq_zero hcd h0' hd' (by norm_num : (0:ℝ) < 1/4)
      refine ⟨δ, hδpos, fun z hz => ?_⟩
      have h := hδspec z hz
      linarith
    choose δ₁ hδ₁pos hδ₁ using h₁
    choose δ₂ hδ₂pos hδ₂ using h₂
    obtain ⟨i₁, -, hi₁⟩ :=
      Finset.exists_min_image Finset.univ (fun i => min (δ₁ i) (δ₂ i)) Finset.univ_nonempty
    refine ⟨min (δ₁ i₁) (δ₂ i₁), lt_min (hδ₁pos i₁) (hδ₂pos i₁), ?_, ?_⟩
    · intro i z hz
      refine hδ₂ i z (le_trans hz ?_)
      exact le_trans (hi₁ i (Finset.mem_univ i)) (min_le_right _ _)
    · intro i z hz
      refine hδ₁ i z (le_trans hz ?_)
      exact le_trans (hi₁ i (Finset.mem_univ i)) (min_le_left _ _)
  obtain ⟨R, hRpos, hRabs, hRder⟩ := hmain
  -- *Step 2*: properties of the maximum `familySup f` on the box `‖z‖ ≤ R`.
  have hM0 : familySup f 0 = 0 := by
    show Finset.sup' Finset.univ Finset.univ_nonempty (fun i => f i 0) = 0
    exact Finset.sup'_eq_of_forall _ _ (fun i _ => hf0 i)
  have hMupper : ∀ z : ℝ × ℝ, ‖z‖ ≤ R → familySup f z ≤ z.1 + ‖z‖ / 4 := by
    intro z hz
    show Finset.sup' Finset.univ Finset.univ_nonempty (fun i => f i z) ≤ z.1 + ‖z‖ / 4
    refine Finset.sup'_le _ _ (fun i _ => ?_)
    have h := (abs_le.mp (hRabs i z hz)).2
    linarith
  have hMlower : ∀ z : ℝ × ℝ, ‖z‖ ≤ R → z.1 - ‖z‖ / 4 ≤ familySup f z := by
    intro z hz
    obtain ⟨i₁, hi₁⟩ := (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty)
    have hsup : f i₁ z ≤ familySup f z := by
      show f i₁ z ≤ Finset.sup' Finset.univ Finset.univ_nonempty (fun i => f i z)
      exact Finset.le_sup' (fun i : ι => f i z) hi₁
    have h := (abs_le.mp (hRabs i₁ z hz)).1
    linarith
  have hMexpand : ∀ x₁ x₂ y : ℝ, |x₁| ≤ R → |x₂| ≤ R → |y| ≤ R → x₁ ≤ x₂ →
      (1/2 : ℝ) * (x₂ - x₁) ≤ familySup f (x₂, y) - familySup f (x₁, y) := by
    intro x₁ x₂ y hx₁ hx₂ hy hlt
    have hderiv : ∀ i : ι, (1/2:ℝ) * (x₂ - x₁) ≤ f i (x₂, y) - f i (x₁, y) := by
      intro i
      exact slice_expanding_le (hf i) (Rx := R) (y := y) (c := 1/2)
        (fun t ht => hRder i (t, y) (by rw [Prod.norm_def]; exact max_le ht hy))
        x₁ x₂ hx₁ hx₂ hlt
    have h1 : Finset.sup' Finset.univ Finset.univ_nonempty
        (fun i => f i (x₁, y) + (1/2) * (x₂ - x₁))
        ≤ Finset.sup' Finset.univ Finset.univ_nonempty (fun i => f i (x₂, y)) :=
      Finset.sup'_mono_fun (fun i _ => by linarith [hderiv i])
    rw [sup'_add_const Finset.univ_nonempty (fun i => f i (x₁, y))
      ((1/2) * (x₂ - x₁))] at h1
    show (1/2) * (x₂ - x₁) ≤ Finset.sup' Finset.univ Finset.univ_nonempty (fun i => f i (x₂, y))
      - Finset.sup' Finset.univ Finset.univ_nonempty (fun i => f i (x₁, y))
    linarith
  -- *Step 3*: the maximum has a unique zero in the box over each `y` in `[-R, R]`.
  have hroot : ∀ y : ℝ, |y| ≤ R → ∃ x : ℝ, |x| ≤ R ∧ familySup f (x, y) = 0 := by
    intro y hy
    have hcont : ContinuousOn (fun x : ℝ => familySup f (x, y)) (Icc (-R) R) :=
      (hMcont.comp (by fun_prop)).continuousOn
    have hnormR : ‖((-R : ℝ), y)‖ = R := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_of_pos hRpos]
      exact max_eq_left hy
    have hnormR' : ‖((R : ℝ), y)‖ = R := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hRpos]
      exact max_eq_left hy
    have hneg : familySup f ((-R), y) < 0 := by
      have h1 : familySup f ((-R : ℝ), y) ≤ (-R : ℝ) + R / 4 := by
        have h := hMupper ((-R : ℝ), y) (le_of_eq hnormR)
        rw [hnormR] at h
        exact h
      linarith
    have hpos : 0 < familySup f ((R : ℝ), y) := by
      have h1 : (R : ℝ) - R / 4 ≤ familySup f ((R : ℝ), y) := by
        have h := hMlower ((R : ℝ), y) (le_of_eq hnormR')
        rw [hnormR'] at h
        exact h
      linarith
    have hmem : (0:ℝ) ∈ Ioo (familySup f ((-R : ℝ), y)) (familySup f ((R : ℝ), y)) :=
      ⟨hneg, hpos⟩
    obtain ⟨x, hx, hval⟩ := intermediate_value_Ioo (show (-R:ℝ) ≤ R by linarith) hcont hmem
    exact ⟨x, le_of_lt (abs_lt.mpr ⟨hx.1, hx.2⟩), hval⟩
  let φ : ℝ → ℝ := fun y => if h : |y| ≤ R then Classical.choose (hroot y h) else 0
  have hφval : ∀ y (h : |y| ≤ R), φ y = Classical.choose (hroot y h) := by
    intro y h
    show (if h' : |y| ≤ R then Classical.choose (hroot y h') else 0) = _
    rw [dif_pos h]
  have hφmem : ∀ y (h : |y| ≤ R), |φ y| ≤ R := by
    intro y h; rw [hφval y h]; exact (Classical.choose_spec (hroot y h)).1
  have hφroot : ∀ y (h : |y| ≤ R), familySup f (φ y, y) = 0 := by
    intro y h; rw [hφval y h]; exact (Classical.choose_spec (hroot y h)).2
  have hφuniq : ∀ y x : ℝ, |y| ≤ R → |x| ≤ R → familySup f (x, y) = 0 → x = φ y := by
    intro y x hy hx hx0
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h := hMexpand x (φ y) y hx (hφmem y hy) hy hlt.le
      rw [hx0, hφroot y hy] at h
      have : 0 < (1/2:ℝ) * (φ y - x) := by linarith
      linarith
    · have h := hMexpand (φ y) x y (hφmem y hy) hx hy hlt.le
      rw [hx0, hφroot y hy] at h
      have : 0 < (1/2:ℝ) * (x - φ y) := by linarith
      linarith
  have hφ0 : φ 0 = 0 := by
    have hM00 : familySup f ((0:ℝ),(0:ℝ)) = 0 := hM0
    have h : (0:ℝ) = φ 0 :=
      hφuniq 0 0 (by simpa using hRpos.le) (by simpa using hRpos.le) hM00
    exact h.symm
  -- *Step 4*: the sign and vanishing conditions.
  have hsign : ∀ x y : ℝ, |x| ≤ R → |y| ≤ R →
      (familySup f (x, y) ≤ 0 ↔ x ≤ φ y) := by
    intro x y hx hy
    constructor
    · intro hle
      by_contra hcon
      rw [not_le] at hcon
      have h := hMexpand (φ y) x y (hφmem y hy) hx hy hcon.le
      rw [hφroot y hy] at h
      have : 0 < (1/2:ℝ) * (x - φ y) := by linarith
      linarith
    · intro hle
      have h := hMexpand x (φ y) y hx (hφmem y hy) hy hle
      rw [hφroot y hy] at h
      linarith
  have hsigneq : ∀ x y : ℝ, |x| ≤ R → |y| ≤ R →
      (familySup f (x, y) = 0 ↔ x = φ y) := fun x y hx hy =>
    ⟨fun h0 => hφuniq y x hy hx h0, fun hxy => by rw [hxy]; exact hφroot y hy⟩
  -- *Step 5*: the slope bound.
  have hslope : ∀ y : ℝ, |y| ≤ R → |φ y| ≤ |y| / 2 := by
    intro y hy
    rcases eq_or_lt_of_le (abs_nonneg y) with h0 | hpos
    · have hy0 : y = 0 := abs_eq_zero.mp h0.symm
      rw [hy0, hφ0, abs_zero]
      norm_num
    · set s : ℝ := |y| / 2 with hsdef
      have hsnn : 0 ≤ s := by rw [hsdef]; linarith [abs_nonneg y]
      have hsle : s ≤ |y| := by rw [hsdef]; linarith [abs_nonneg y]
      have hsabs : |s| ≤ R := by rw [abs_of_nonneg hsnn, hsdef]; linarith
      have hnorm_s : ‖((s:ℝ), y)‖ = |y| := by
        rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hsnn]
        exact max_eq_right hsle
      have hnorm_ns : ‖(((-s):ℝ), y)‖ = |y| := by
        rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_of_nonneg hsnn]
        exact max_eq_right hsle
      have hMs : 0 < familySup f (s, y) := by
        have h1 : (s : ℝ) - |y| / 4 ≤ familySup f (s, y) := by
          have h := hMlower (s, y) (by rw [hnorm_s]; exact hy)
          rwa [hnorm_s] at h
        linarith
      have hMns : familySup f (-s, y) < 0 := by
        have h1 : familySup f (-s, y) ≤ -s + |y| / 4 := by
          have h := hMupper ((-s), y) (by rw [hnorm_ns]; exact hy)
          rwa [hnorm_ns] at h
        linarith
      have h1 : -s ≤ φ y := by
        refine (hsign (-s) y ?_ hy).mp (le_of_lt hMns)
        rw [abs_neg]; exact hsabs
      have h2 : φ y < s := by
        by_contra hcon
        rw [not_lt] at hcon
        have hle : familySup f (s, y) ≤ 0 := (hsign s y hsabs hy).mpr hcon
        linarith
      have h3 : |φ y| ≤ s := abs_le.mpr ⟨by linarith, le_of_lt h2⟩
      exact h3
  -- *Step 6*: continuity of `φ` on the open interval.
  have hcont : ContinuousOn φ (Ioo (-R) R) :=
    continuousOn_of_expanding hMcont (by norm_num) hMexpand
      (fun y hy => hφmem y hy) (fun y hy => hφroot y hy)
  exact ⟨R, R, hRpos, hRpos, φ, hφ0, hcont, hslope,
    fun x y hx hy => ⟨hsign x y hx hy, hsigneq x y hx hy⟩⟩

end Work.Drive.Mono
