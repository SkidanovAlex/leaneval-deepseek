import Mathlib

/-!
# Green's identity for a harmonic function against a compactly supported test function

The main result `Work.Analysis.Harmonic.integral_inner_gradient_eq_zero` states that if `h` is
harmonic on the (compact) support of a `C^1` compactly supported function `φ : ℂ → ℝ`, then
`∫ ∇h · ∇φ = 0`.

The proof is a standard two-step reduction.

* `exists_contDiff_eqOn_one_of_isCompact_subset_isOpen`: a smooth cutoff function equal to `1` on a
  neighbourhood of a compact set `K` and supported in a prescribed open neighbourhood `U` of `K`.
* `integral_inner_gradient_eq_neg_integral_laplacian`: Green's first identity
  `∫ ∇H · ∇φ = -∫ φ ΔH` for `H` of class `C²`, obtained as a sum of one-dimensional integrations by
  parts in the directions of an orthonormal basis of `ℂ`, together with the standard formula
  expressing the Laplacian as the sum of the second derivatives along such a basis.

Given these, one replaces `h` by `ψ * h`, where `ψ` is a smooth cutoff that is `1` on a neighbourhood
of `tsupport φ` and vanishes off the open set `{z | HarmonicAt h z}`; the product is of class `C²`,
agrees with `h` near `tsupport φ` (so the integrands agree pointwise), and has vanishing Laplacian on
`tsupport φ` (so the remaining integral `∫ φ Δ(ψ * h)` vanishes identically).
-/

namespace Work.Analysis.Harmonic

open MeasureTheory Laplacian
open scoped Topology Gradient

/-! ## Elementary facts about gradients -/

/-- The gradient of a function is supported in the (topological) support of the function. -/
lemma tsupport_gradient_subset (f : ℂ → ℝ) : tsupport (gradient f) ⊆ tsupport f :=
  (tsupport_comp_subset (g := (InnerProductSpace.toDual ℝ ℂ).symm) (by simp) (fderiv ℝ f)).trans
    (tsupport_fderiv_subset ℝ)

/-- If `z` is outside the topological support of `f`, then the gradient of `f` vanishes at `z`. -/
lemma gradient_eq_zero_of_notMem_tsupport {f : ℂ → ℝ} {z : ℂ} (hz : z ∉ tsupport f) :
    gradient f z = 0 := by
  have heq : f =ᶠ[𝓝 z] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hz] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [Filter.EventuallyEq.gradient_eq heq, gradient_fun_const]

/-- The directional derivative `z ↦ Df(z)(v)` of a compactly supported function is compactly
supported. -/
lemma hasCompactSupport_fderiv_apply {f : ℂ → ℝ} (hf : HasCompactSupport f) (v : ℂ) :
    HasCompactSupport (fun z ↦ fderiv ℝ f z v) := by
  have hsub : tsupport (fun z ↦ fderiv ℝ f z v) ⊆ tsupport f :=
    (tsupport_comp_subset (g := fun w : ℂ →L[ℝ] ℝ ↦ w v) (by simp) (fderiv ℝ f)).trans
      (tsupport_fderiv_subset ℝ)
  exact IsCompact.of_isClosed_subset hf (isClosed_tsupport _) hsub

/-! ## Smooth cutoffs -/

/-- **Smooth Urysohn lemma.** For a compact set `K` contained in an open set `U` of a
finite-dimensional real normed space there is a `C²` function `ψ` with `tsupport ψ ⊆ U` which is
equal to `1` on an open neighbourhood `V` of `K`. -/
theorem exists_contDiff_eqOn_one_of_isCompact_subset_isOpen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ψ : E → ℝ, ContDiff ℝ 2 ψ ∧ tsupport ψ ⊆ U ∧
      ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ Set.EqOn ψ 1 V := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, contDiff_const, by simp, ∅, isOpen_empty, by simp⟩
  choose ψ hψsupp hψcs hψC hψrange hψone using
    fun x : K => exists_contDiff_tsupport_subset (n := 2) (hU.mem_nhds (hKU x.2))
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => Function.support (ψ x))
    (fun x => (hψC x).continuous.isOpen_support)
    (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩,
      by rw [Function.mem_support, hψone ⟨z, hz⟩]; exact one_ne_zero⟩)
  set f : E → ℝ := fun z => ∑ i ∈ t, ψ i z with hfdef
  have hfC : ContDiff ℝ 2 f := by
    rw [hfdef]; exact ContDiff.sum (fun i _ => hψC i)
  have hfpos : ∀ z ∈ K, 0 < f z := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (ht hz)
    obtain ⟨hit, hiz⟩ := Set.mem_iUnion.1 hi
    rw [hfdef]
    have hlt : 0 < ψ i z := lt_of_le_of_ne ((hψrange i (Set.mem_range_self z)).1) (Ne.symm hiz)
    exact lt_of_lt_of_le hlt
      (Finset.single_le_sum (fun j _ => (hψrange j (Set.mem_range_self z)).1) hit)
  obtain ⟨z₀, hz₀K, hz₀min⟩ := hK.exists_isMinOn hKne hfC.continuous.continuousOn
  set m : ℝ := f z₀ with hmdef
  have hmpos : 0 < m := by rw [hmdef]; exact hfpos z₀ hz₀K
  have hmin : ∀ z ∈ K, m ≤ f z := by intro z hz; rw [hmdef]; exact hz₀min hz
  refine ⟨fun z => Real.smoothTransition (4 * f z / m - 1), ?_, ?_, {z | m / 2 < f z},
    isOpen_lt continuous_const hfC.continuous, ?_, ?_⟩
  · fun_prop
  · have hsupp : Function.support (fun z => Real.smoothTransition (4 * f z / m - 1)) ⊆
        ⋃ i ∈ t, Function.support (ψ i) := by
      intro z hz
      have h1 : 0 < 4 * f z / m - 1 := by
        by_contra h
        exact hz (Real.smoothTransition.zero_of_nonpos (not_lt.mp h))
      have h2 : 0 < 4 * f z / m := by linarith
      have hfz : 0 < f z := by
        have h3 : 0 < 4 * f z := (div_pos_iff_of_pos_right hmpos).mp h2
        linarith
      obtain ⟨i, hit, hiz⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := t)
        (f := fun i => ψ i z) (by rw [hfdef] at hfz; exact ne_of_gt hfz)
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hit, hiz⟩⟩
    calc tsupport (fun z => Real.smoothTransition (4 * f z / m - 1))
        = closure (Function.support (fun z => Real.smoothTransition (4 * f z / m - 1))) := rfl
      _ ⊆ closure (⋃ i ∈ t, Function.support (ψ i)) := closure_mono hsupp
      _ ⊆ ⋃ i ∈ t, tsupport (ψ i) := by
          refine closure_minimal ?_ (isClosed_biUnion_finset fun i _ => isClosed_tsupport _)
          intro z hz
          obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
          obtain ⟨hit, hiz⟩ := Set.mem_iUnion.1 hi
          exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hit, subset_tsupport _ hiz⟩⟩
      _ ⊆ U := by
          intro z hz
          obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
          obtain ⟨hit, hiz⟩ := Set.mem_iUnion.1 hi
          exact hψsupp i hiz
  · intro z hz
    have hz' : m ≤ f z := hmin z hz
    show m / 2 < f z
    linarith
  · intro z hz
    show Real.smoothTransition (4 * f z / m - 1) = 1
    have hz' : m / 2 < f z := hz
    have h4 : (2 : ℝ) ≤ 4 * f z / m := by
      rw [le_div_iff₀ hmpos]
      linarith
    exact Real.smoothTransition.one_of_one_le (by linarith)

/-! ## Green's identity -/

/-- The function `z ↦ fderiv ℝ H z v` is `C¹` when `H` is `C²`. -/
lemma contDiff_fderiv_apply {H : ℂ → ℝ} (hH : ContDiff ℝ 2 H) (v : ℂ) :
    ContDiff ℝ 1 (fun z ↦ fderiv ℝ H z v) := by fun_prop

/-- The second derivative of `H` in the direction `v` is the second iterated derivative. -/
lemma fderiv_fderiv_apply_eq (H : ℂ → ℝ) (hH : ContDiff ℝ 2 H) (z v : ℂ) :
    fderiv ℝ (fun y ↦ fderiv ℝ H y v) z v = iteratedFDeriv ℝ 2 H z ![v, v] := by
  rw [show (fun y ↦ fderiv ℝ H y v) = (ContinuousLinearMap.apply ℝ ℝ v) ∘ (fderiv ℝ H) from
    funext fun y => (ContinuousLinearMap.apply_apply v (fderiv ℝ H y)).symm]
  rw [fderiv_comp z]
  · rw [(ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ ℝ v)).fderiv]
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, iteratedFDeriv_two_apply]
    simp
  · exact (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ ℝ v)).differentiableAt
  · exact ((hH.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero).differentiableAt

/-- Integrability of one summand of Green's formula. -/
lemma integrable_fderiv_apply_mul {H φ : ℂ → ℝ} (hH : ContDiff ℝ 2 H) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (v : ℂ) :
    Integrable (fun z ↦ fderiv ℝ H z v * fderiv ℝ φ z v) := by
  refine Continuous.integrable_of_hasCompactSupport ?_
    (HasCompactSupport.mul_left (hasCompactSupport_fderiv_apply hφc v))
  exact (contDiff_fderiv_apply hH v).continuous.mul (by fun_prop)

/-- Integrability of the other summand of Green's formula. -/
lemma integrable_iteratedFDeriv_mul {H φ : ℂ → ℝ} (hH : ContDiff ℝ 2 H) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (v : ℂ) :
    Integrable (fun z ↦ iteratedFDeriv ℝ 2 H z ![v, v] * φ z) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.mul_left hφc)
  exact (by fun_prop : Continuous (fun z ↦ iteratedFDeriv ℝ 2 H z ![v, v])).mul hφ.continuous

/-- One-dimensional integration by parts in the direction `v`, with the second derivative written as
an iterated derivative. -/
lemma integral_fderiv_apply_mul {H φ : ℂ → ℝ} (hH : ContDiff ℝ 2 H) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (v : ℂ) :
    ∫ z, fderiv ℝ H z v * fderiv ℝ φ z v
      = - ∫ z, iteratedFDeriv ℝ 2 H z ![v, v] * φ z := by
  have hD : ContDiff ℝ 1 (fun z ↦ fderiv ℝ H z v) := contDiff_fderiv_apply hH v
  have hDcont : Continuous (fun z ↦ fderiv ℝ H z v) := hD.continuous
  have hD'cont : Continuous (fun z ↦ fderiv ℝ (fun y ↦ fderiv ℝ H y v) z v) := by fun_prop
  have hfφv : HasCompactSupport (fun z ↦ fderiv ℝ φ z v) := hasCompactSupport_fderiv_apply hφc v
  have hφcont : Continuous φ := hφ.continuous
  have hibp : ∫ z, fderiv ℝ H z v * fderiv ℝ φ z v
      = - ∫ z, fderiv ℝ (fun y ↦ fderiv ℝ H y v) z v * φ z := by
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := v) ?_ ?_ ?_ ?_ ?_
    · refine Continuous.integrable_of_hasCompactSupport (hD'cont.mul hφcont) ?_
      exact HasCompactSupport.mul_left hφc
    · refine Continuous.integrable_of_hasCompactSupport (hDcont.mul (by fun_prop)) ?_
      exact HasCompactSupport.mul_left hfφv
    · refine Continuous.integrable_of_hasCompactSupport (hDcont.mul hφcont) ?_
      exact HasCompactSupport.mul_left hφc
    · intro x hx; exact (hD.differentiable one_ne_zero).differentiableAt
    · intro x hx; exact (hφ.differentiable one_ne_zero).differentiableAt
  rw [hibp]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  rw [fderiv_fderiv_apply_eq H hH z v]

/-- **Green's first identity** on `ℂ`, without boundary term: for `H` of class `C²` and `φ` of class
`C¹` with compact support, `∫ ∇H · ∇φ = - ∫ φ ΔH`. -/
theorem integral_inner_gradient_eq_neg_integral_laplacian {H φ : ℂ → ℝ}
    (hH : ContDiff ℝ 2 H) (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∫ (z : ℂ), inner (𝕜 := ℝ) (gradient H z) (gradient φ z)
      = - ∫ (z : ℂ), Laplacian.laplacian H z * φ z := by
  have h_expand : (fun z : ℂ ↦ inner (𝕜 := ℝ) (gradient H z) (gradient φ z))
      = fun z ↦ ∑ i, fderiv ℝ H z (Complex.orthonormalBasisOneI i)
          * fderiv ℝ φ z (Complex.orthonormalBasisOneI i) := by
    funext z
    rw [← OrthonormalBasis.sum_inner_mul_inner Complex.orthonormalBasisOneI (gradient H z)
      (gradient φ z)]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_gradient_left]
    congr 1
    rw [real_inner_comm, inner_gradient_left]
  rw [h_expand, integral_finsetSum Finset.univ
    (fun i _ ↦ integrable_fderiv_apply_mul hH hφ hφc _)]
  simp only [integral_fderiv_apply_mul hH hφ hφc]
  rw [Finset.sum_neg_distrib]
  congr 1
  have hrw : (fun z : ℂ ↦ Laplacian.laplacian H z * φ z)
      = fun z ↦ ∑ i, iteratedFDeriv ℝ 2 H z ![Complex.orthonormalBasisOneI i,
            Complex.orthonormalBasisOneI i] * φ z := by
    funext z
    rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis H
      Complex.orthonormalBasisOneI) z, Finset.sum_mul]
  rw [hrw, integral_finsetSum Finset.univ (fun i _ ↦ integrable_iteratedFDeriv_mul hH hφ hφc _)]

/-! ## The main theorem -/

/-- **Green's identity for a harmonic function.**  If `h` is harmonic on the support of a compactly
supported `C¹` function `φ : ℂ → ℝ`, then `∫ ∇h · ∇φ = 0`. -/
theorem integral_inner_gradient_eq_zero {h φ : ℂ → ℝ}
    (hh : ∀ z ∈ tsupport φ, InnerProductSpace.HarmonicAt h z)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∫ (z : ℂ), inner (𝕜 := ℝ) (gradient h z) (gradient φ z) = 0 := by
  obtain ⟨ψ, hψC, hψsupp, V, hVopen, hKV, hψV⟩ :=
    exists_contDiff_eqOn_one_of_isCompact_subset_isOpen (K := tsupport φ)
      (U := {z | InnerProductSpace.HarmonicAt h z}) hφc
      (InnerProductSpace.isOpen_setOfPred_harmonicAt h) hh
  set H : ℂ → ℝ := fun z => ψ z * h z with hHdef
  have hHC : ContDiff ℝ 2 H := by
    rw [hHdef]
    refine contDiff_iff_contDiffAt.mpr fun z => ?_
    by_cases hz : z ∈ tsupport ψ
    · exact hψC.contDiffAt.mul (hψsupp hz).1
    · have hzero : (fun y => ψ y * h y) =ᶠ[𝓝 z] 0 := by
        filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hz] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy]
        simp
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  have hHeq : ∀ z ∈ tsupport φ, H =ᶠ[𝓝 z] h := by
    intro z hz
    filter_upwards [hVopen.mem_nhds (hKV hz)] with y hy
    show ψ y * h y = h y
    rw [hψV hy, Pi.one_apply, one_mul]
  have hpoint : ∀ z, inner (𝕜 := ℝ) (gradient h z) (gradient φ z)
      = inner (𝕜 := ℝ) (gradient H z) (gradient φ z) := by
    intro z
    by_cases hz : gradient φ z = 0
    · rw [hz, inner_zero_right, inner_zero_right]
    · have hzK : z ∈ tsupport φ :=
        tsupport_gradient_subset φ (subset_closure (by rwa [Function.mem_support]))
      rw [(hHeq z hzK).gradient_eq]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_inner_gradient_eq_neg_integral_laplacian hHC hφ hφc]
  have hzero : ∀ z, Laplacian.laplacian H z * φ z = 0 := by
    intro z
    by_cases hz : φ z = 0
    · rw [hz, mul_zero]
    · have hzK : z ∈ tsupport φ := subset_tsupport φ (by rwa [Function.mem_support])
      have h1 : Laplacian.laplacian H z = Laplacian.laplacian h z :=
        (InnerProductSpace.laplacian_congr_nhds (hHeq z hzK)).eq_of_nhds
      have h2 : Laplacian.laplacian h z = 0 := (hh z hzK).2.eq_of_nhds
      rw [h1, h2, zero_mul]
  have hΦzero : (fun z : ℂ => Laplacian.laplacian H z * φ z) = 0 := funext hzero
  simp [hΦzero]

end Work.Analysis.Harmonic
