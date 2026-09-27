import Mathlib
import Submission.Work.Drive.Whitney.whitneyDiscDefs
import Submission.Work.Projection.dimH_image_le_of_contDiffOn
import Submission.Work.Projection.exists_countable_chart_cover_general
import Submission.Work.Projection.Defs
import Submission.Work.Projection.exists_good_direction
import Submission.Work.Projection.mfderiv_chartAt_decomp

namespace Work.Drive.Whitney

open scoped Manifold ContDiff ENNReal
open Topology MeasureTheory Set

noncomputable section

/-!
# Hausdorff dimension of the upper transversality-bad parameters

The set `Work.Drive.Whitney.badTransTop f γ₁ γ₂` of translation parameters `v` for which the
candidate Whitney disc fails to be transverse to `f` at some point of the upper edge `u = 1` is
contained in a countable union of images of `C^1` maps defined on open subsets of
`ℝ × ℝⁿ × (3 · 2n)`, whose `finrank` is `7 n + 1`; hence its Hausdorff dimension is at most
`7 n + 1`.

The parametrisation is as follows.  Cover the manifold by the charts at the points `p i`.  For a
parameter `v` and a witness `x ∈ (-1,1)` with `γ₂ (sigR x)` in the source of the `i`-th chart, the
explicit form of the bad condition reads
`f (γ₂ (sigR x)) - f (γ₁ (sigR x)) + ∑ k, (bumpU1 k x) • v k ∈ range (mfderiv f (γ₂ (sigR x)))`.
The chain rule in chart coordinates (`Work.Projection.mfderiv_chartAt_decomp`) turns the last
membership into membership in the range of `fderiv ℝ (chartRep f (p i)) (chart (γ₂ (sigR x)))`,
which is a linear map on `ℝⁿ`; writing `a` for a preimage, the equation
`A a = c x + ∑ k, bumpU1 k x • v k` determines the `(0,0)`-block of `v` (the coefficient
`bumpU1 (0,0) x` does not vanish on `(-1,1)`), while the three other blocks are free.  So `v` is a
value of the map `(x, a, w) ↦ v` on the open set
`{x ∈ (-1,1) | γ₂ (sigR x) ∈ source of the i-th chart} × univ × univ`.

The development is structured as

* `chartRepGen` — the chart representation of `f` at `p`, for an arbitrary target dimension;
* `transDom`, `transFun` — the domain and the parametrising map;
* `contDiffOn_transFun`, `isOpen_transDom` — smoothness on an open domain;
* `badTransTop_subset` — the covering;
* `finrank_PSpace` — the dimension count;
* `dimH_badTransTop` — the result.
-/

namespace DimHTransTopAux

/-- The four bumps are indexed by `Fin 2 × Fin 2`; `WIdx` is the set of the three indices different
from `(0,0)`. -/
abbrev WIdx : Type := {k : Fin 2 × Fin 2 // k ≠ (0, 0)}

/-- The source of the chartwise parametrisation: the curve parameter `x`, the vector `a ∈ ℝⁿ`
parametrising the range of the chart derivative, and the three remaining bump blocks. -/
abbrev PSpace (n : ℕ) : Type :=
  ℝ × EuclideanSpace ℝ (Fin n) × (WIdx → EuclideanSpace ℝ (Fin (2 * n)))

/-- The target of the parametrisation: the translation parameters. -/
abbrev QSpace (n : ℕ) : Type := (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))

/-- The chart representation of `f` at `p`, for an arbitrary target dimension. -/
def chartRepGen {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N)) (p : M) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N) :=
  fun y => f ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y)

/-- The sum over the four indices splits into the three free blocks and the `(0,0)`-block. -/
lemma sum_split {n : ℕ} (g : Fin 2 × Fin 2 → EuclideanSpace ℝ (Fin (2 * n))) :
    (∑ k : Fin 2 × Fin 2, g k) = (∑ k' : WIdx, g k'.1) + g (0, 0) := by
  have h : (∑ k ∈ Finset.univ.erase (0, 0), g k) = ∑ k' : WIdx, g k'.1 :=
    Finset.sum_subtype _ (fun k => by simp [Finset.mem_erase]) g
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0, 0)), h]

/-- `(2 : ℕ∞ω) ≤ ∞`. -/
lemma two_le_top : (2 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  show ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
  exact WithTop.coe_le_coe.mpr le_top

/-- `(1 : ℕ∞ω) ≤ ∞`. -/
lemma one_le_top : (1 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  show ((1 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
  exact WithTop.coe_le_coe.mpr le_top

lemma continuous_sigR : Continuous sigR := by
  have h : sigR = fun x : ℝ => (1 / 2) * x + 1 / 2 := by
    funext x; simp [sigR]; ring
  rw [h]; fun_prop

lemma contMDiff_sigR : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
    ((⊤ : ℕ∞) : WithTop ℕ∞) sigR := by
  rw [contMDiff_iff_contDiff]
  have h : sigR = fun x : ℝ => (1 / 2) * x + 1 / 2 := by
    funext x; simp [sigR]; ring
  rw [h]; fun_prop

/-- The chart at `p`, composed with the curve `γ ∘ sigR`, is smooth wherever the curve meets the
source of the chart. -/
lemma contDiffOn_chartAt_comp_sigR {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {γ : ℝ → M}
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (p : M) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => (chartAt (EuclideanSpace ℝ (Fin n)) p) (γ (sigR x)))
      {x : ℝ | γ (sigR x) ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source} := by
  have h1 : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => γ (sigR x)) := hγ.comp contMDiff_sigR
  have h2 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (chartAt (EuclideanSpace ℝ (Fin n)) p)
      (chartAt (EuclideanSpace ℝ (Fin n)) p).source := contMDiffOn_chart
  exact (h2.comp (h1.contMDiffOn.mono (Set.subset_univ _)) (fun x hx => hx)).contDiffOn

/-- The chart representation is smooth on the target of the chart. -/
lemma contDiffOn_chartRepGen {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {N : ℕ} (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) ((⊤ : ℕ∞) : WithTop ℕ∞) f) (p : M) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chartRepGen f p)
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target := by
  have h : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (f ∘ (chartAt (EuclideanSpace ℝ (Fin n)) p).symm)
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target :=
    (hf.contMDiffOn (s := Set.univ)).comp (contMDiffOn_chart_symm (x := p))
      (by intro x hx; trivial)
  rw [show chartRepGen f p = f ∘ (chartAt (EuclideanSpace ℝ (Fin n)) p).symm from rfl]
  exact h.contDiffOn

/-- The derivative of the chart representation is `C^1` on the target of the chart. -/
lemma contDiffOn_fderiv_chartRepGen {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {N : ℕ} (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) ((⊤ : ℕ∞) : WithTop ℕ∞) f) (p : M) :
    ContDiffOn ℝ 1 (fun y : EuclideanSpace ℝ (Fin n) => fderiv ℝ (chartRepGen f p) y)
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target :=
  ((contDiffOn_chartRepGen f hf p).of_le two_le_top).fderiv_of_isOpen
    (chartAt (EuclideanSpace ℝ (Fin n)) p).open_target (by norm_num)

/-- `f` composed with a smooth curve (reparametrised by `sigR`) is smooth. -/
lemma contDiff_f_comp_curve {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {N : ℕ} (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {γ : ℝ → M}
    (hγ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => f (γ (sigR x))) :=
  (hf.comp (hγ.comp contMDiff_sigR)).contDiff

/-- The `u`-derivative `bumpU1 k` of a disc bump is `C^1`. -/
lemma contDiff_bumpU1 (k : Fin 2 × Fin 2) : ContDiff ℝ 1 (bumpU1 k) := by
  have h2 : ContDiff ℝ 2 (discBump k) := (contDiff_discBump k).of_le two_le_top
  have h3 : ContDiff ℝ 1 (fderiv ℝ (discBump k)) := h2.fderiv_right (by norm_num)
  have h4 : ContDiff ℝ 1 (fun x : ℝ => fderiv ℝ (discBump k) (x, 1)) :=
    h3.comp (contDiff_id.prodMk contDiff_const)
  have h5 : ContDiff ℝ 1 (fun x : ℝ => fderiv ℝ (discBump k) (x, 1) (0, 1)) :=
    h4.clm_apply contDiff_const
  exact h5

/-- The finrank of the space of the three free blocks is `6 n`. -/
lemma card_widx : Fintype.card WIdx = 3 := by
  rw [Fintype.card_subtype]; decide

lemma finrank_fun_widx (n : ℕ) :
    Module.finrank ℝ (WIdx → EuclideanSpace ℝ (Fin (2 * n))) = 6 * n := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, card_widx,
    finrank_euclideanSpace_fin]
  simp only [nsmul_eq_mul]
  ring

/-- The finrank of the parametrising space is `7 n + 1`. -/
lemma finrank_PSpace (n : ℕ) : Module.finrank ℝ (PSpace n) = 7 * n + 1 := by
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self,
    finrank_euclideanSpace_fin, finrank_fun_widx]
  ring

/-- The domain of the chartwise parametrisation of the upper-edge bad parameters. -/
def transDom (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (γ₂ : ℝ → M) (p : ℕ → M) (i : ℕ) : Set (PSpace n) :=
  {q | q.1 ∈ Ioo (-1 : ℝ) 1 ∧
    γ₂ (sigR q.1) ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source}

lemma isOpen_transDom (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (γ₂ : ℝ → M) (hγ₂ : Continuous γ₂) (p : ℕ → M) (i : ℕ) :
    IsOpen (transDom n γ₂ p i) := by
  have h1 : IsOpen {q : PSpace n | q.1 ∈ Set.Ioo (-1 : ℝ) 1} :=
    isOpen_Ioo.preimage continuous_fst
  have h2 : IsOpen {q : PSpace n | γ₂ (sigR q.1) ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source} :=
    (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).open_source.preimage
      (hγ₂.comp (continuous_sigR.comp continuous_fst))
  exact h1.inter h2

/-- The chartwise parametrisation of the upper-edge bad parameters. -/
def transFun {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M) (p : ℕ → M) (i : ℕ) :
    PSpace n → QSpace n :=
  fun q k =>
    if hk : k = (0, 0) then
      (bumpU1 (0, 0) q.1)⁻¹ •
        ((fderiv ℝ (chartRepGen f (p i))
              ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR q.1)))) q.2.1
          - (f (γ₂ (sigR q.1)) - f (γ₁ (sigR q.1)))
          - ∑ k' : WIdx, bumpU1 k'.1 q.1 • q.2.2 k')
    else q.2.2 ⟨k, hk⟩

lemma transFun_apply_zero {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M) (p : ℕ → M)
    (i : ℕ) (q : PSpace n) :
    transFun f γ₁ γ₂ p i q (0, 0) =
      (bumpU1 (0, 0) q.1)⁻¹ •
        ((fderiv ℝ (chartRepGen f (p i))
              ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR q.1)))) q.2.1
          - (f (γ₂ (sigR q.1)) - f (γ₁ (sigR q.1)))
          - ∑ k' : WIdx, bumpU1 k'.1 q.1 • q.2.2 k') := by
  simp only [transFun]
  rw [dif_pos trivial]

lemma transFun_apply_of_ne {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M) (p : ℕ → M)
    (i : ℕ) {k : Fin 2 × Fin 2} (hk : k ≠ (0, 0)) (q : PSpace n) :
    transFun f γ₁ γ₂ p i q k = q.2.2 ⟨k, hk⟩ := by
  simp only [transFun]
  rw [dif_neg hk]

/-- The parametrising map is `C^1` on its (open) domain. -/
lemma contDiffOn_transFun {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (γ₁ γ₂ : ℝ → M)
    (hγ₁ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (p : ℕ → M) (i : ℕ) :
    ContDiffOn ℝ 1 (transFun f γ₁ γ₂ p i) (transDom n γ₂ p i) := by
  have hfst : ContDiffOn ℝ 1 (fun q : PSpace n => q.1) (transDom n γ₂ p i) :=
    contDiff_fst.contDiffOn.mono (Set.subset_univ _)
  have hsw : ContDiffOn ℝ 1 (fun q : PSpace n => q.2.2) (transDom n γ₂ p i) :=
    (contDiff_snd.comp contDiff_snd).contDiffOn.mono (Set.subset_univ _)
  have hsa : ContDiffOn ℝ 1 (fun q : PSpace n => q.2.1) (transDom n γ₂ p i) :=
    (contDiff_fst.comp contDiff_snd).contDiffOn.mono (Set.subset_univ _)
  have hchart : ContDiffOn ℝ 1
      (fun q : PSpace n => (chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR q.1)))
      (transDom n γ₂ p i) :=
    ((contDiffOn_chartAt_comp_sigR hγ₂ (p i)).of_le one_le_top).comp hfst (fun q hq => hq.2)
  have hA : ContDiffOn ℝ 1
      (fun q : PSpace n => fderiv ℝ (chartRepGen f (p i))
        ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR q.1))))
      (transDom n γ₂ p i) :=
    (contDiffOn_fderiv_chartRepGen f hf (p i)).comp hchart
      (fun q hq => (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).map_source hq.2)
  have hAa : ContDiffOn ℝ 1
      (fun q : PSpace n => (fderiv ℝ (chartRepGen f (p i))
        ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR q.1)))) q.2.1)
      (transDom n γ₂ p i) := hA.clm_apply hsa
  have hf2 : ContDiffOn ℝ 1 (fun q : PSpace n => f (γ₂ (sigR q.1)))
      (transDom n γ₂ p i) :=
    ((contDiff_f_comp_curve f hf hγ₂).of_le one_le_top).contDiffOn.comp (t := Set.univ) hfst
      (fun _ _ => Set.mem_univ _)
  have hf1 : ContDiffOn ℝ 1 (fun q : PSpace n => f (γ₁ (sigR q.1)))
      (transDom n γ₂ p i) :=
    ((contDiff_f_comp_curve f hf hγ₁).of_le one_le_top).contDiffOn.comp (t := Set.univ) hfst
      (fun _ _ => Set.mem_univ _)
  have hc : ContDiffOn ℝ 1
      (fun q : PSpace n => f (γ₂ (sigR q.1)) - f (γ₁ (sigR q.1)))
      (transDom n γ₂ p i) := hf2.sub hf1
  have hS : ContDiffOn ℝ 1
      (fun q : PSpace n => ∑ k' : WIdx, bumpU1 k'.1 q.1 • q.2.2 k')
      (transDom n γ₂ p i) := by
    refine ContDiffOn.sum (fun k' _ => ?_)
    have h1 : ContDiffOn ℝ 1 (fun q : PSpace n => bumpU1 k'.1 q.1) (transDom n γ₂ p i) :=
      (contDiff_bumpU1 k'.1).contDiffOn.comp (t := Set.univ) hfst (fun _ _ => Set.mem_univ _)
    have h2 : ContDiffOn ℝ 1 (fun q : PSpace n => q.2.2 k') (transDom n γ₂ p i) := by
      refine ((ContinuousLinearMap.proj (R := ℝ) k').contDiff.comp_contDiffOn hsw).congr
        (fun q hq => ?_)
      rw [Function.comp_apply, ContinuousLinearMap.proj_apply]
    exact h1.smul h2
  have hInv : ContDiffOn ℝ 1 (fun q : PSpace n => (bumpU1 (0, 0) q.1)⁻¹)
      (transDom n γ₂ p i) := by
    refine ContDiffOn.inv ?_ ?_
    · exact (contDiff_bumpU1 (0, 0)).contDiffOn.comp (t := Set.univ) hfst (fun _ _ => Set.mem_univ _)
    · intro q hq; exact bumpU1_zero_ne hq.1
  rw [contDiffOn_pi]
  intro k
  by_cases hk : k = (0, 0)
  · subst hk
    rw [show (fun q : PSpace n => transFun f γ₁ γ₂ p i q (0, 0)) =
        (fun q : PSpace n => (bumpU1 (0, 0) q.1)⁻¹ •
          ((fderiv ℝ (chartRepGen f (p i))
              ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR q.1)))) q.2.1
            - (f (γ₂ (sigR q.1)) - f (γ₁ (sigR q.1)))
            - ∑ k' : WIdx, bumpU1 k'.1 q.1 • q.2.2 k'))
        from funext (fun q => transFun_apply_zero f γ₁ γ₂ p i q)]
    exact hInv.smul ((hAa.sub hc).sub hS)
  · rw [show (fun q : PSpace n => transFun f γ₁ γ₂ p i q k) =
        (fun q : PSpace n => q.2.2 ⟨k, hk⟩)
        from funext (fun q => transFun_apply_of_ne f γ₁ γ₂ p i hk q)]
    refine ((ContinuousLinearMap.proj (R := ℝ) ⟨k, hk⟩).contDiff.comp_contDiffOn hsw).congr
      (fun q hq => ?_)
    rw [Function.comp_apply, ContinuousLinearMap.proj_apply]

/-- **Covering.**  Every upper-edge-bad translation parameter arises as a value of the
parametrisation of one of the charts. -/
lemma badTransTop_subset {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (γ₁ γ₂ : ℝ → M) (p : ℕ → M)
    (hcov : (Set.univ : Set M) ⊆ ⋃ i, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source) :
    badTransTop f γ₁ γ₂ ⊆ ⋃ i, transFun f γ₁ γ₂ p i '' transDom n γ₂ p i := by
  rintro v ⟨x, hx, hv⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ (γ₂ (sigR x))))
  obtain ⟨z, hz⟩ := hv
  have hdec := Work.Projection.mfderiv_chartAt_decomp f hf (p i) (γ₂ (sigR x)) hi
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  set a : EuclideanSpace ℝ (Fin n) :=
    mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR x)) z with ha
  set wblock : WIdx → EuclideanSpace ℝ (Fin (2 * n)) := fun k' => v k'.1 with hw
  refine ⟨(x, a, wblock), ?_, ?_⟩
  · show x ∈ Set.Ioo (-1 : ℝ) 1 ∧ γ₂ (sigR x) ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source
    exact ⟨hx, hi⟩
  · have hkey : (fderiv ℝ (chartRepGen f (p i))
        ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR x)))) a
      = f (γ₂ (sigR x)) - f (γ₁ (sigR x)) + ∑ k : Fin 2 × Fin 2, bumpU1 k x • v k := by
      rw [ha]
      rw [show (fderiv ℝ (chartRepGen f (p i))
            ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR x))))
          = fderiv ℝ (fun y => f ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)).symm y))
            ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR x))) from rfl]
      rw [← hz, hdec]
      rfl
    funext k
    by_cases hk : k = (0, 0)
    · subst hk
      rw [transFun_apply_zero]
      change (bumpU1 (0, 0) x)⁻¹ •
          ((fderiv ℝ (chartRepGen f (p i))
              ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR x)))) a
            - (f (γ₂ (sigR x)) - f (γ₁ (sigR x)))
            - ∑ k' : WIdx, bumpU1 k'.1 x • wblock k')
        = v (0, 0)
      have hsum := sum_split (fun k : Fin 2 × Fin 2 => bumpU1 k x • v k)
      have hcalc : (fderiv ℝ (chartRepGen f (p i))
          ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR x)))) a
          - (f (γ₂ (sigR x)) - f (γ₁ (sigR x)))
          - ∑ k' : WIdx, bumpU1 k'.1 x • wblock k'
        = bumpU1 (0, 0) x • v (0, 0) := by
        simp only [hw]
        rw [hkey, hsum]
        abel
      rw [hcalc, inv_smul_smul₀ (bumpU1_zero_ne hx)]
    · rw [transFun_apply_of_ne f γ₁ γ₂ p i hk]

end DimHTransTopAux

/-- **Hausdorff-dimension bound for the upper transversality-bad parameters.**
(The result should live in namespace `Work.Drive.Whitney`.)

`Work.Drive.Whitney.badTransTop f γ₁ γ₂` (defined in
`Submission.Work.Drive.Whitney.whitneyDiscDefs`) is the set of translation parameters `v` for which
`fderiv ℝ (discMap f γ₁ γ₂ v) (x,1) (0,1)` lies in `range (mfderiv f (γ₂ (sigR x)))` for some
`x ∈ (-1,1)` (equivalently, in the explicit form used in the definition:
`(f (γ₂ (sigR x)) - f (γ₁ (sigR x))) + ∑ k, (bumpU1 k x) • v k ∈ range (mfderiv f (γ₂ (sigR x)))`).

Proof design: cover `M` by countably many charts.  For `x` whose `γ₂ (sigR x)` lies in the source
of the `i`-th chart one has
`range (mfderiv f (γ₂ (sigR x))) ⊆ range (fderiv ℝ (chartRep f (p i)) (chart (γ₂ (sigR x))))`
(chain rule `Work.Projection.mfderiv_chartAt_decomp_apply`).  Since `bumpU1 (0,0) x ≠ 0` on
`(-1,1)` (`Work.Drive.Whitney.bumpU1_zero_ne`), a bad `v` is recovered from `(x, a, w)`, `a ∈ ℝⁿ`
the vector parametrising the range and `w` the three other blocks, by solving for the `(0,0)`-block.
So `badTransTop` is contained in the countable union over `i` of the images of the `C^1` maps
`(x, a, w) ↦ v` defined on the open subset
`{x ∈ Ioo (-1) 1 | γ₂ (sigR x) ∈ (chartAt _ (p i)).source} × univ × univ` of
`ℝ × EuclideanSpace ℝ (Fin n) × ({k : Fin 2 × Fin 2 // k ≠ (0,0)} → EuclideanSpace ℝ (Fin (2 * n)))`,
whose `finrank` is `1 + n + 3 * (2 * n) = 7 * n + 1`.  Then
`Work.Projection.dimH_image_le_of_contDiffOn` and `dimH_iUnion` give the bound. -/
theorem dimH_badTransTop {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
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
    dimH (Work.Drive.Whitney.badTransTop f γ₁ γ₂) ≤ ((7 * n + 1 : ℕ) : ENNReal) := by
  classical
  haveI : Nonempty M := ⟨γ₁ 0⟩
  obtain ⟨p, hcov⟩ := Work.Projection.exists_countable_chart_cover_general
    (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (M := M)
  calc dimH (badTransTop f γ₁ γ₂)
      ≤ dimH (⋃ i, DimHTransTopAux.transFun f γ₁ γ₂ p i ''
          DimHTransTopAux.transDom n γ₂ p i) :=
        dimH_mono (DimHTransTopAux.badTransTop_subset f hf γ₁ γ₂ p hcov)
    _ = ⨆ i, dimH (DimHTransTopAux.transFun f γ₁ γ₂ p i ''
          DimHTransTopAux.transDom n γ₂ p i) := dimH_iUnion _
    _ ≤ ((7 * n + 1 : ℕ) : ENNReal) := by
        refine iSup_le fun i => ?_
        calc dimH (DimHTransTopAux.transFun f γ₁ γ₂ p i ''
              DimHTransTopAux.transDom n γ₂ p i)
            ≤ (Module.finrank ℝ (DimHTransTopAux.PSpace n) : ENNReal) :=
              Work.Projection.dimH_image_le_of_contDiffOn
                (DimHTransTopAux.isOpen_transDom n γ₂ hγ₂.continuous p i)
                (DimHTransTopAux.contDiffOn_transFun f hf γ₁ γ₂ hγ₁ hγ₂ p i)
                (Set.Subset.refl _)
          _ = ((7 * n + 1 : ℕ) : ENNReal) := by
              rw [DimHTransTopAux.finrank_PSpace]

end

end Work.Drive.Whitney
