import Mathlib
import Submission.Work.Drive.Whitney.whitneyDiscDefs
import Submission.Work.Projection.dimH_image_le_of_contDiffOn
import Submission.Work.Projection.exists_countable_chart_cover_general
import Submission.Work.Projection.Defs
import Submission.Work.Projection.exists_good_direction

namespace Work.Drive.Whitney

open scoped Manifold ContDiff Topology
open Set Metric Topology

noncomputable section

/-! ## The chartwise parametrisation of the lower transversality-bad parameters -/

/-- The four bump indices with the distinguished index `(0,0)` removed. -/
abbrev FreeIdx : Type := {k : Fin 2 × Fin 2 // k ≠ ((0 : Fin 2), (0 : Fin 2))}

/-- The parametrising space of the lower transversality-bad parameters of a single chart. -/
abbrev TransParamSpace (n : ℕ) : Type :=
  ℝ × EuclideanSpace ℝ (Fin n) × (FreeIdx → EuclideanSpace ℝ (Fin (2 * n)))

/-- The set of parameters `x` for which the first arc point lies in the source of the chart
centred at `p`. -/
def arcSource (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (γ₁ : ℝ → M) (p : M) : Set ℝ :=
  {x | γ₁ (sigR x) ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source}

/-- The chart coordinates of the first arc at the chart centred at `p`. -/
def chartPt (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (γ₁ : ℝ → M) (p : M) (x : ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  (chartAt (EuclideanSpace ℝ (Fin n)) p) (γ₁ (sigR x))

/-- The chart representation of `f` in the target dimension `2 * n`. -/
def chartRep2 (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (p : M) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)) :=
  fun y => f ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y)

/-- The derivative of the chart representation of `f` at the chart coordinates of the first
arc. -/
def chartDeriv (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (γ₁ : ℝ → M) (p : M) (x : ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
  fderiv ℝ (chartRep2 n f p) (chartPt n γ₁ p x)

/-- The difference of the images of the two arcs at the parameter `x`. -/
def arcDiff (n : ℕ) {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M)
    (x : ℝ) : EuclideanSpace ℝ (Fin (2 * n)) :=
  f (γ₂ (sigR x)) - f (γ₁ (sigR x))

/-- The open domain of the chartwise parametrisation: the parameters `x` in the open interval
whose first arc point lies in the source of the chart, together with the whole of the other two
factors. -/
def transDom (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (γ₁ : ℝ → M) (p : M) :
    Set (TransParamSpace n) :=
  {q | q.1 ∈ Set.Ioo (-1 : ℝ) 1 ∧ q.1 ∈ arcSource n γ₁ p}

/-- The chartwise parametrisation of the lower transversality-bad parameters: the `(0,0)`-block of
the parameter is recovered from the parameter `x`, the vector `a` parametrising the range of the
chart derivative and the three other blocks, using that `bumpU (0,0) x ≠ 0` on `(-1,1)`. -/
def transParam (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (γ₁ γ₂ : ℝ → M) (p : M) :
    TransParamSpace n → (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n)) :=
  fun q k =>
    if h : k = (0, 0) then
      (bumpU (0, 0) q.1)⁻¹ •
        (chartDeriv n f γ₁ p q.1 q.2.1 - arcDiff n f γ₁ γ₂ q.1
          - ∑ k' : FreeIdx, (bumpU k'.1 q.1) • q.2.2 k')
    else q.2.2 ⟨k, h⟩

/-- The dimension of the parametrising space is `1 + n + 3 * (2 * n) = 7 * n + 1`. -/
lemma finrank_transParamSpace (n : ℕ) :
    Module.finrank ℝ (TransParamSpace n) = 7 * n + 1 := by
  change Module.finrank ℝ
    (ℝ × (EuclideanSpace ℝ (Fin n) × (FreeIdx → EuclideanSpace ℝ (Fin (2 * n))))) = 7 * n + 1
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_pi_fintype,
    finrank_euclideanSpace_fin, finrank_euclideanSpace_fin, Module.finrank_self]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hcard : Fintype.card FreeIdx = 3 := by decide
  rw [hcard]
  omega

/-! ## Smoothness of the parametrisation -/

/-- The affine reparametrisation `sigR` is smooth. -/
lemma contMDiff_sigR : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ sigR := by
  rw [contMDiff_iff_contDiff]
  unfold sigR
  fun_prop

private lemma one_le_infty : (1 : ℕ∞ω) ≤ ∞ := by
  show ((1 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
  exact WithTop.coe_le_coe.mpr le_top

private lemma two_le_infty : (2 : ℕ∞ω) ≤ ∞ := by
  show ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
  exact WithTop.coe_le_coe.mpr le_top

/-- The `u`-derivative of any bump is smooth. -/
lemma contDiff_bumpU_whitney (k : Fin 2 × Fin 2) : ContDiff ℝ ∞ (bumpU k) := by
  have h : bumpU k = fun x : ℝ => xAlpha k.2 x := funext fun x => bumpU_eq k x
  rw [h]
  exact contDiff_xAlpha k.2

/-- The chart representation of `f` is smooth on the target of the chart at `p`. -/
lemma contDiffOn_chartRep_two (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f) (p : M) :
    ContDiffOn ℝ ∞ (chartRep2 n f p) (chartAt (EuclideanSpace ℝ (Fin n)) p).target := by
  have h : ContMDiffOn (𝓡 n) (𝓡 (2 * n)) ∞
      (f ∘ (chartAt (EuclideanSpace ℝ (Fin n)) p).symm)
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target :=
    (hf.contMDiffOn (s := Set.univ)).comp (contMDiffOn_chart_symm (x := p))
      (fun x _ => Set.mem_univ _)
  change ContDiffOn ℝ ∞
    (fun y : EuclideanSpace ℝ (Fin n) => f ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y))
    (chartAt (EuclideanSpace ℝ (Fin n)) p).target
  simpa [Function.comp_def] using h.contDiffOn

/-- The chart coordinates of the first arc form a smooth map on the chart source. -/
lemma contDiffOn_chartPt (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (γ₁ : ℝ → M) (hγ₁ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ₁) (p : M) :
    ContDiffOn ℝ ∞ (chartPt n γ₁ p) (arcSource n γ₁ p) := by
  have hcomp : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞
      ((chartAt (EuclideanSpace ℝ (Fin n)) p) ∘ (γ₁ ∘ sigR)) (arcSource n γ₁ p) :=
    (contMDiffOn_chart (I := 𝓡 n) (x := p)).comp (hγ₁.comp contMDiff_sigR).contMDiffOn
      (fun x hx => hx)
  change ContDiffOn ℝ ∞ (fun x : ℝ =>
      (chartAt (EuclideanSpace ℝ (Fin n)) p) ((γ₁ ∘ sigR) x)) (arcSource n γ₁ p)
  simpa [Function.comp_def] using contMDiffOn_iff_contDiffOn.mp hcomp

/-- The derivative of the chart representation of `f`, evaluated at the chart coordinates of
the first arc, is smooth. -/
lemma contDiffOn_chartDeriv (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (γ₁ : ℝ → M) (hγ₁ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ₁) (p : M) :
    ContDiffOn ℝ 1 (chartDeriv n f γ₁ p) (arcSource n γ₁ p) := by
  have h2 : ContDiffOn ℝ 2 (chartRep2 n f p)
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target :=
    (contDiffOn_chartRep_two n f hf p).of_le two_le_infty
  have hF : ContDiffOn ℝ 1
      (fun y : EuclideanSpace ℝ (Fin n) => fderiv ℝ (chartRep2 n f p) y)
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target :=
    h2.fderiv_of_isOpen (chartAt (EuclideanSpace ℝ (Fin n)) p).open_target (by norm_num)
  have hca : ContDiffOn ℝ 1 (chartPt n γ₁ p) (arcSource n γ₁ p) :=
    (contDiffOn_chartPt n γ₁ hγ₁ p).of_le one_le_infty
  have hcomp := hF.comp hca (fun x hx => (chartAt (EuclideanSpace ℝ (Fin n)) p).map_source hx)
  exact hcomp

/-- The difference of the arc images is smooth. -/
lemma contDiff_arcDiff (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (γ₁ γ₂ : ℝ → M) (hγ₁ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ₁)
    (hγ₂ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ₂) :
    ContDiff ℝ ∞ (arcDiff n f γ₁ γ₂) := by
  have h1 : ContDiff ℝ ∞ (fun x : ℝ => f (γ₂ (sigR x))) :=
    ((hf.comp hγ₂).comp contMDiff_sigR).contDiff
  have h2 : ContDiff ℝ ∞ (fun x : ℝ => f (γ₁ (sigR x))) :=
    ((hf.comp hγ₁).comp contMDiff_sigR).contDiff
  rw [show arcDiff n f γ₁ γ₂ = fun x : ℝ => f (γ₂ (sigR x)) - f (γ₁ (sigR x)) from rfl]
  exact h1.sub h2

/-- The domain of the chartwise parametrisation is open. -/
lemma isOpen_transDom (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (γ₁ : ℝ → M) (hγ₁ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ₁) (p : M) :
    IsOpen (transDom n γ₁ p) := by
  have hcont : Continuous (fun q : TransParamSpace n => γ₁ (sigR q.1)) :=
    hγ₁.continuous.comp (contMDiff_sigR.continuous.comp continuous_fst)
  have h1 : IsOpen {q : TransParamSpace n | q.1 ∈ Set.Ioo (-1 : ℝ) 1} :=
    isOpen_Ioo.preimage continuous_fst
  have h2 : IsOpen {q : TransParamSpace n | γ₁ (sigR q.1) ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) p).source} :=
    (chartAt (EuclideanSpace ℝ (Fin n)) p).open_source.preimage hcont
  have hset : transDom n γ₁ p = {q : TransParamSpace n | q.1 ∈ Set.Ioo (-1 : ℝ) 1} ∩
      {q : TransParamSpace n | γ₁ (sigR q.1) ∈
        (chartAt (EuclideanSpace ℝ (Fin n)) p).source} := by
    ext q; simp [transDom, arcSource]
  rw [hset]
  exact h1.inter h2

/-- The chartwise parametrisation is `C^1` on its open domain. -/
lemma contDiffOn_transParam (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (γ₁ γ₂ : ℝ → M) (hγ₁ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ₁)
    (hγ₂ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ₂) (p : M) :
    ContDiffOn ℝ 1 (transParam n f γ₁ γ₂ p) (transDom n γ₁ p) := by
  rw [contDiffOn_pi]
  intro k
  by_cases hk : k = (0, 0)
  · simp only [transParam, dif_pos hk]
    have hchart := contDiffOn_chartDeriv n f hf γ₁ hγ₁ p
    have hA : ContDiffOn ℝ 1
        (fun q : TransParamSpace n => (bumpU (0, 0) q.1)⁻¹) (transDom n γ₁ p) := by
      have hbump : ContDiffOn ℝ 1 (fun q : TransParamSpace n => bumpU (0, 0) q.1)
          (transDom n γ₁ p) :=
        ((contDiff_bumpU_whitney (0, 0)).of_le one_le_infty).contDiffOn.comp contDiffOn_fst
          (fun q _ => Set.mem_univ _)
      exact hbump.inv (fun q hq => bumpU_zero_ne hq.1)
    have hB : ContDiffOn ℝ 1
        (fun q : TransParamSpace n => chartDeriv n f γ₁ p q.1 q.2.1) (transDom n γ₁ p) :=
      (hchart.comp contDiffOn_fst (fun q hq => hq.2)).clm_apply
        (contDiffOn_fst.comp contDiffOn_snd (fun q _ => Set.mem_univ _))
    have hC : ContDiffOn ℝ 1
        (fun q : TransParamSpace n => arcDiff n f γ₁ γ₂ q.1) (transDom n γ₁ p) :=
      ((contDiff_arcDiff n f hf γ₁ γ₂ hγ₁ hγ₂).of_le one_le_infty).contDiffOn.comp
        contDiffOn_fst (fun q _ => Set.mem_univ _)
    have hD : ContDiffOn ℝ 1
        (fun q : TransParamSpace n =>
          ∑ k' : FreeIdx, (bumpU k'.1 q.1) • q.2.2 k') (transDom n γ₁ p) := by
      refine ContDiffOn.sum (s := Finset.univ) (fun k' _ => ?_)
      have hb : ContDiffOn ℝ 1 (fun q : TransParamSpace n => bumpU k'.1 q.1)
          (transDom n γ₁ p) :=
        ((contDiff_bumpU_whitney k'.1).of_le one_le_infty).contDiffOn.comp contDiffOn_fst
          (fun q _ => Set.mem_univ _)
      have hw : ContDiffOn ℝ 1 (fun q : TransParamSpace n => q.2.2 k') (transDom n γ₁ p) := by
        fun_prop
      exact hb.smul hw
    exact hA.smul ((hB.sub hC).sub hD)
  · simp only [transParam, dif_neg hk]
    fun_prop

/-! ## The bad parameters are covered by the chartwise parametrisations -/

/-- Splitting a sum over the four bump indices into the distinguished index and the rest. -/
lemma transSum_split {E : Type*} [AddCommMonoid E] (F : (Fin 2 × Fin 2) → E) :
    (∑ k, F k) = F (0, 0) + ∑ k' : FreeIdx, F k'.1 := by
  have herase : (∑ k ∈ (Finset.univ.erase (0, 0) : Finset (Fin 2 × Fin 2)), F k)
      = ∑ k' : FreeIdx, F k'.1 :=
    Finset.sum_subtype (p := fun k : Fin 2 × Fin 2 => k ≠ (0, 0)) _ (fun x => by simp) F
  have hsplit : (∑ k : Fin 2 × Fin 2, F k)
      = (∑ k ∈ (Finset.univ.erase (0, 0) : Finset (Fin 2 × Fin 2)), F k) + F (0, 0) :=
    (Finset.sum_erase_add (Finset.univ) F (Finset.mem_univ (0, 0))).symm
  rw [hsplit, herase]
  exact add_comm _ _

/-- The chain rule for the specific target dimension `2 * n`. -/
lemma mfderiv_chartAt_decomp_apply_two (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (p x : M) (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (z : TangentSpace (𝓡 n) x) :
    mfderiv (𝓡 n) (𝓡 (2 * n)) f x z =
      fderiv ℝ (chartRep2 n f p) ((chartAt (EuclideanSpace ℝ (Fin n)) p) x)
        (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) x z) := by
  rw [Work.Projection.mfderiv_chartAt_decomp f hf p x hx]
  rfl

/-- Every lower transversality-bad parameter occurs as a value of the chartwise parametrisation
of one of the charts of a cover. -/
lemma badTransBot_subset_iUnion (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (γ₁ γ₂ : ℝ → M) (p : ℕ → M)
    (hcov : (Set.univ : Set M) ⊆ ⋃ i, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source) :
    badTransBot f γ₁ γ₂ ⊆ ⋃ i, transParam n f γ₁ γ₂ (p i) '' transDom n γ₁ (p i) := by
  intro v hv
  obtain ⟨x, hx, hz⟩ := hv
  obtain ⟨z', hz'⟩ := hz
  have hmem : γ₁ (sigR x) ∈ ⋃ i, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source :=
    hcov (Set.mem_univ _)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
  have hchain := mfderiv_chartAt_decomp_apply_two n f hf (p i) (γ₁ (sigR x)) hi z'
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  refine ⟨(x, mfderiv (𝓡 n) (𝓡 n)
      (chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₁ (sigR x)) z', fun k => v k.1),
    ⟨hx, hi⟩, ?_⟩
  have hDa : chartDeriv n f γ₁ (p i) x
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₁ (sigR x)) z')
      = arcDiff n f γ₁ γ₂ x + ∑ k : Fin 2 × Fin 2, (bumpU k x) • v k := by
    have h1 : chartDeriv n f γ₁ (p i) x
        (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₁ (sigR x)) z')
        = mfderiv (𝓡 n) (𝓡 (2 * n)) f (γ₁ (sigR x)) z' := by
      simp only [chartDeriv, chartPt]
      exact hchain.symm
    exact h1.trans hz'
  have hS : (∑ k : Fin 2 × Fin 2, (bumpU k x) • v k)
      = bumpU (0, 0) x • v (0, 0) + ∑ k' : FreeIdx, (bumpU k'.1 x) • v k'.1 :=
    transSum_split _
  funext k
  by_cases hk : k = (0, 0)
  · simp only [transParam, dif_pos hk]
    rw [hDa, hS, hk]
    have hcancel : (arcDiff n f γ₁ γ₂ x
          + (bumpU (0, 0) x • v (0, 0) + ∑ k' : FreeIdx, (bumpU k'.1 x) • v k'.1))
        - arcDiff n f γ₁ γ₂ x - ∑ k' : FreeIdx, (bumpU k'.1 x) • v k'.1
        = bumpU (0, 0) x • v (0, 0) := by abel
    rw [hcancel, inv_smul_smul₀ (bumpU_zero_ne hx)]
  · simp only [transParam, dif_neg hk]

/-! ## The dimension bound -/

/-- **Hausdorff-dimension bound for the lower transversality-bad parameters.**
(The result should live in namespace `Work.Drive.Whitney`.)

`Work.Drive.Whitney.badTransBot f γ₁ γ₂` (defined in
`Submission.Work.Drive.Whitney.whitneyDiscDefs`) is the set of translation parameters `v` for which
`fderiv ℝ (discMap f γ₁ γ₂ v) (x,0) (0,1)` lies in `range (mfderiv f (γ₁ (sigR x)))` for some
`x ∈ (-1,1)` (equivalently, in the explicit form used in the definition:
`(f (γ₂ (sigR x)) - f (γ₁ (sigR x))) + ∑ k, (bumpU k x) • v k ∈ range (mfderiv f (γ₁ (sigR x)))`).

Proof design: cover `M` by countably many charts.  For `x` whose `γ₁ (sigR x)` lies in the source
of the `i`-th chart one has
`range (mfderiv f (γ₁ (sigR x))) ⊆ range (fderiv ℝ (chartRep f (p i)) (chart (γ₁ (sigR x))))`
(the chart derivative is the missing factor in the chain rule
`Work.Projection.mfderiv_chartAt_decomp_apply`, so the range of `mfderiv f` is contained in the
range of the chart representation's derivative).  Since `bumpU (0,0) x ≠ 0` on `(-1,1)`
(`Work.Drive.Whitney.bumpU_zero_ne`), a bad `v` is recovered from `(x, a, w)`, `a ∈ ℝⁿ` the vector
parametrising the range and `w` the three other blocks, by solving for the `(0,0)`-block.  So
`badTransBot` is contained in the countable union over `i` of the images of the `C^1` maps
`(x, a, w) ↦ v` defined on the open subset
`{x ∈ Ioo (-1) 1 | γ₁ (sigR x) ∈ (chartAt _ (p i)).source} × univ × univ` of
`ℝ × EuclideanSpace ℝ (Fin n) × ({k : Fin 2 × Fin 2 // k ≠ (0,0)} → EuclideanSpace ℝ (Fin (2 * n)))`,
whose `finrank` is `1 + n + 3 * (2 * n) = 7 * n + 1`.  Then
`Work.Projection.dimH_image_le_of_contDiffOn` and `dimH_iUnion` give the bound. -/
theorem dimH_badTransBot {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (γ₁ γ₂ : ℝ → M)
    (hγ₁ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂) :
    dimH (Work.Drive.Whitney.badTransBot f γ₁ γ₂) ≤ ((7 * n + 1 : ℕ) : ENNReal) := by
  have hMne : Nonempty M := ⟨γ₁ 0⟩
  obtain ⟨p, hp⟩ := Work.Projection.exists_countable_chart_cover_general
    (E := EuclideanSpace ℝ (Fin n)) (H := EuclideanSpace ℝ (Fin n)) (I := 𝓡 n) (M := M)
  have hsub := badTransBot_subset_iUnion n f hf γ₁ γ₂ p hp
  calc dimH (Work.Drive.Whitney.badTransBot f γ₁ γ₂)
      ≤ dimH (⋃ i, transParam n f γ₁ γ₂ (p i) '' transDom n γ₁ (p i)) := dimH_mono hsub
    _ = ⨆ i, dimH (transParam n f γ₁ γ₂ (p i) '' transDom n γ₁ (p i)) := dimH_iUnion _
    _ ≤ ((7 * n + 1 : ℕ) : ENNReal) := by
        refine iSup_le fun i => ?_
        calc dimH (transParam n f γ₁ γ₂ (p i) '' transDom n γ₁ (p i))
            ≤ (Module.finrank ℝ (TransParamSpace n) : ENNReal) :=
              Work.Projection.dimH_image_le_of_contDiffOn (isOpen_transDom n γ₁ hγ₁ (p i))
                (contDiffOn_transParam n f hf γ₁ γ₂ hγ₁ hγ₂ (p i)) Set.Subset.rfl
          _ = ((7 * n + 1 : ℕ) : ENNReal) := by rw [finrank_transParamSpace]

end

end Work.Drive.Whitney
