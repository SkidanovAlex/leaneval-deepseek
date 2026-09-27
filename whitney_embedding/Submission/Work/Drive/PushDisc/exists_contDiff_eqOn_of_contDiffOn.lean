import Mathlib

/-!
# Extending a `C^∞` function off an open set

If `K` is a compact subset of an open set `U` in a finite-dimensional real normed space `E`, and
`g : E → F` is `C^∞` on `U`, then `g` agrees on `K` with a globally `C^∞` function `S` whose
derivative also agrees with that of `g` on `K`.

The construction is the standard cut-off argument:

* for every `x ∈ K` the lemma `exists_contDiff_tsupport_subset` (applied to the neighbourhood `U`
  of `x`) produces a smooth bump `b x` with `tsupport (b x) ⊆ U` and `b x x = 1`;
* compactness of `K` yields finitely many points `t ⊆ K` with `K ⊆ ⋃ i ∈ t, {b i > 1/2}`;
* `W := ∑ i ∈ t, b i` is smooth, nonnegative, with `tsupport W ⊆ U` (a finite union of closed sets)
  and `W > 1/2` on the open neighbourhood `⋃ i ∈ t, {b i > 1/2}` of `K`;
* `χ := Real.smoothTransition ∘ (2 * W)` is smooth, is `1` where `W > 1/2` (in particular on a
  neighbourhood of `K`) and is `0` outside `tsupport W ⊆ U`;
* `S := χ • g` is `C^∞`: on the open set `U` it is the product of two smooth functions, while off
  the closed set `tsupport χ ⊆ U` it vanishes identically.

Since `S = g` on a neighbourhood of `K`, both the values and the Fréchet derivatives agree on `K`.
-/

namespace Work.Drive.PushDisc

open Set Metric Filter

theorem exists_contDiff_eqOn_of_contDiffOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {g : E → F}
    (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g U) :
    ∃ S : E → F, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S ∧
      (∀ x ∈ K, S x = g x) ∧ (∀ x ∈ K, fderiv ℝ S x = fderiv ℝ g x) := by
  classical
  -- Step 1: a smooth bump at every point of `K`, supported in `U`.
  have hbump : ∀ x ∈ K, ∃ b : E → ℝ, tsupport b ⊆ U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b ∧ Set.range b ⊆ Set.Icc (0:ℝ) 1 ∧ b x = 1 := by
    intro x hx
    obtain ⟨b, h1, -, h3, h4, h5⟩ :=
      exists_contDiff_tsupport_subset (s := U) (x := x) (n := (⊤ : ℕ∞)) (hU.mem_nhds (hKU hx))
    exact ⟨b, h1, h3, h4, h5⟩
  choose b hbts hbsm hbrange hbone using hbump
  -- Step 2: a finite subcover of `K` by the sets `{b x > 1/2}`.
  have hcover : K ⊆ ⋃ i : {x // x ∈ K}, {y : E | (1:ℝ)/2 < b i.1 i.2 y} := by
    intro y hy
    refine mem_iUnion.mpr ⟨⟨y, hy⟩, ?_⟩
    show (1:ℝ)/2 < b y hy y
    rw [hbone y hy]
    norm_num
  obtain ⟨t, ht⟩ :=
    hK.elim_finite_subcover (fun i : {x // x ∈ K} => {y : E | (1:ℝ)/2 < b i.1 i.2 y})
      (fun i => isOpen_lt continuous_const (hbsm i.1 i.2).continuous) hcover
  let β : {x // x ∈ K} → E → ℝ := fun i => b i.1 i.2
  let W : E → ℝ := fun y => ∑ i ∈ t, β i y
  have hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W := by
    have h := ContDiff.sum (𝕜 := ℝ) (n := ((⊤:ℕ∞) : WithTop ℕ∞)) (s := t)
      (f := β) (fun i _ => hbsm i.1 i.2)
    simpa [W] using h
  have hWsupp : Function.support W ⊆ U := by
    intro y hy
    by_contra hyU
    have hzero : W y = 0 := Finset.sum_eq_zero (fun i _ => by
      by_contra h
      exact hyU (hbts i.1 i.2 (subset_tsupport _ (Function.mem_support.mpr h))))
    exact (Function.mem_support.mp hy) hzero
  have htsW : tsupport W ⊆ U := by
    have h1 : Function.support W ⊆ ⋃ i ∈ t, tsupport (β i) := by
      intro y hy
      have h2 : ¬ (∀ i ∈ t, β i y = 0) := fun h ↦ Function.mem_support.mp hy (by
        show (∑ i ∈ t, β i y) = 0
        exact Finset.sum_eq_zero h)
      push Not at h2
      obtain ⟨i, hi, hiy⟩ := h2
      exact Set.mem_biUnion hi (subset_tsupport _ (Function.mem_support.mpr hiy))
    have hclosed : IsClosed (⋃ i ∈ t, tsupport (β i)) :=
      isClosed_biUnion_finset (fun i _ => isClosed_tsupport _)
    have h3 : tsupport W ⊆ ⋃ i ∈ t, tsupport (β i) := closure_minimal h1 hclosed
    exact h3.trans (Set.iUnion₂_subset (fun i _ => hbts i.1 i.2))
  -- Step 3: the cut-off `χ`.
  let χ : E → ℝ := Real.smoothTransition ∘ fun y => 2 * W y
  have hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
    have h2W : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => 2 * W y) :=
      contDiff_const.mul hWsm
    exact (Real.smoothTransition.contDiff (n := ⊤)).comp h2W
  have hχone : ∀ y, (1:ℝ)/2 < W y → χ y = 1 := by
    intro y hy
    show Real.smoothTransition (2 * W y) = 1
    exact Real.smoothTransition.one_of_one_le (by linarith)
  have hχzero : ∀ y ∉ U, χ y = 0 := by
    intro y hy
    have hWy : W y = 0 := by
      by_contra h
      exact hy (hWsupp (Function.mem_support.mpr h))
    show Real.smoothTransition (2 * W y) = 0
    rw [hWy, mul_zero, Real.smoothTransition.zero]
  have hχsupp : Function.support χ ⊆ Function.support W := by
    intro y hy
    simp only [Function.mem_support] at hy ⊢
    exact fun h ↦ hy (by
      rw [show χ y = Real.smoothTransition (2 * W y) from rfl, h, mul_zero,
        Real.smoothTransition.zero])
  have htsχ : tsupport χ ⊆ U :=
    (closure_mono hχsupp).trans htsW
  -- Step 4: the extension.
  refine ⟨fun y => χ y • g y, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact hχsm.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds hx))
    · have hx' : x ∈ (tsupport χ)ᶜ := fun h => hx (htsχ h)
      have hopen : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
      refine (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hx'] with y hy
      have hyχ : χ y = 0 := by
        by_contra h
        exact hy (subset_tsupport χ (Function.mem_support.mpr h))
      simp [hyχ]
  · intro x hxK
    obtain ⟨i, hi, hiy⟩ := Set.mem_iUnion₂.mp (ht hxK)
    have hiy' : (1:ℝ)/2 < β i x := hiy
    have hle : β i x ≤ W x :=
      Finset.single_le_sum (fun j _ => (hbrange j.1 j.2 (Set.mem_range_self x)).1) hi
    have hχx : χ x = 1 := hχone x (by linarith)
    simp [hχx]
  · intro x hxK
    have hWopen : IsOpen (⋃ i ∈ t, {y : E | (1:ℝ)/2 < β i y}) :=
      isOpen_biUnion (fun i _ => isOpen_lt continuous_const (hbsm i.1 i.2).continuous)
    have hev : (fun y => χ y • g y) =ᶠ[nhds x] g := by
      filter_upwards [hWopen.mem_nhds (ht hxK)] with y hy
      obtain ⟨i, hi, hiy⟩ := Set.mem_iUnion₂.mp hy
      have hiy' : (1:ℝ)/2 < β i y := hiy
      have hle : β i y ≤ W y :=
        Finset.single_le_sum (fun j _ => (hbrange j.1 j.2 (Set.mem_range_self y)).1) hi
      have hχy : χ y = 1 := hχone y (by linarith)
      simp [hχy]
    exact Filter.EventuallyEq.fderiv_eq hev

end Work.Drive.PushDisc
