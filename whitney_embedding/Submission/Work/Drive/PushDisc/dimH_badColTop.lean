import Mathlib
import Submission.Work.Drive.PushDisc.lensColTopDefs
import Submission.Work.Drive.PushDisc.lensBump_fderiv
import Submission.Work.Projection.dimH_image_le_of_contDiffOn
import Submission.Work.Projection.exists_countable_chart_cover_general
import Submission.Work.Projection.mfderiv_chartAt_decomp

/-!
# Hausdorff dimension of the upper-collar-bad parameters of the lens perturbation

`Work.Drive.PushDisc.badColTop f Δ₀ ρ γ₂` is the set of perturbation parameters `v` for which the
vertical derivative `fderiv ℝ (lensMap Δ₀ ρ v) (x, arch x) (0, 1)` at the upper edge of the lens
meets the tangent space of `f` at the point `γ₂ (sigR x)` of the second arc, for some
`x ∈ (-1,1)`.

Here it is shown that `dimH (badColTop f Δ₀ ρ γ₂) ≤ 7 * n + 1`.  The proof covers `M` by countably
many charts and, at the `i`-th chart, parametrises the bad parameters by the *source*

    ℝ × ℝⁿ × ({k : Fin 2 × Fin 2 // k ≠ (0,0)} → ℝ^{2n}),

of real dimension `1 + n + 3 * (2n) = 7n + 1`: the first coordinate is the edge parameter `x`, the
second a vector `a` parametrising the range of the chart derivative of `f`, and the remaining three
are the three free blocks of `v`.  The `(0,0)`-block is then solved from the linear relation

    fderiv ℝ (chartRep) (chart (γ₂ (sigR x))) a = baseDeriv x + ∑ k, edgeTop ρ k x • v k,

using that `edgeTop ρ (0,0) x = fderiv ℝ (lensBump ρ (0,0)) (x, arch x) (0,1)` does not vanish for
`|x| < 1` (this is `edgeTop_zero_ne`, and needs `0 < ρ`).
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff ENNReal
open Set Metric MeasureTheory Topology Filter

noncomputable section

open Work.Drive.Whitney (sigR)

namespace DimHColTopAux

/-- The four bump indices are `Fin 2 × Fin 2`; `WIdx` is the set of the three indices different
from `(0,0)`. -/
abbrev WIdx : Type := {k : Fin 2 × Fin 2 // k ≠ (0, 0)}

/-- The source of the chartwise parametrisation: the edge parameter `x`, the vector `a ∈ ℝⁿ`
parametrising the range of the chart derivative, and the three remaining bump blocks. -/
abbrev PSpace (n : ℕ) : Type :=
  ℝ × EuclideanSpace ℝ (Fin n) × (WIdx → EuclideanSpace ℝ (Fin (2 * n)))

/-- The sum over the four indices splits into the three free blocks and the `(0,0)`-block. -/
lemma sum_split {n : ℕ} (g : Fin 2 × Fin 2 → EuclideanSpace ℝ (Fin (2 * n))) :
    (∑ k : Fin 2 × Fin 2, g k) = (∑ k' : WIdx, g k'.1) + g (0, 0) := by
  have h : (∑ k ∈ Finset.univ.erase (0, 0), g k) = ∑ k' : WIdx, g k'.1 :=
    Finset.sum_subtype _ (fun k => by simp [Finset.mem_erase]) g
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0, 0)), h]

lemma two_le_top : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  exact WithTop.coe_le_coe.mpr le_top

lemma one_le_top : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  show ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  exact WithTop.coe_le_coe.mpr le_top

/-- The affine reparametrisation `sigR` is smooth. -/
lemma contMDiff_sigR : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
    ((⊤ : ℕ∞) : WithTop ℕ∞) sigR := by
  rw [contMDiff_iff_contDiff]
  have h : sigR = fun x : ℝ => (1 / 2) * x + 1 / 2 := by
    funext x; simp [sigR]; ring
  rw [h]; fun_prop

/-- The chart representation of `f` at `p`, in the target dimension `2 * n`. -/
def chartRep2' {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (p : M) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)) :=
  fun y => f ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y)

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

/-- The chart representation of `f` is smooth on the target of the chart at `p`. -/
lemma contDiffOn_chartRep2' {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (p : M) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chartRep2' f p)
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target := by
  have h : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (f ∘ (chartAt (EuclideanSpace ℝ (Fin n)) p).symm)
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target :=
    (hf.contMDiffOn (s := Set.univ)).comp (contMDiffOn_chart_symm (x := p))
      (by intro x hx; trivial)
  rw [show chartRep2' f p = f ∘ (chartAt (EuclideanSpace ℝ (Fin n)) p).symm from rfl]
  exact h.contDiffOn

/-- The derivative of the chart representation is `C^1` on the target of the chart. -/
lemma contDiffOn_fderiv_chartRep2' {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (p : M) :
    ContDiffOn ℝ 1 (fun y : EuclideanSpace ℝ (Fin n) => fderiv ℝ (chartRep2' f p) y)
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target :=
  ((contDiffOn_chartRep2' f hf p).of_le two_le_top).fderiv_of_isOpen
    (chartAt (EuclideanSpace ℝ (Fin n)) p).open_target (by norm_num)

/-! ## The base term and the edge derivatives -/

/-- The arch of the lens is smooth. -/
lemma contDiff_arch : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) arch := by
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => 1 - x ^ 2)
  fun_prop

/-- The `(0,1)`-derivative of the base map `Δ₀` at the upper edge. -/
def baseDeriv {n : ℕ} (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (x : ℝ) :
    EuclideanSpace ℝ (Fin (2 * n)) :=
  fderiv ℝ Δ₀ (x, arch x) (0, 1)

/-- The base term `baseDeriv` is `C^1` (in fact `C^∞`). -/
lemma contDiff_baseDeriv {n : ℕ} {Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    (hΔ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀) :
    ContDiff ℝ 1 (baseDeriv Δ₀) := by
  have h2 : ContDiff ℝ 2 Δ₀ := hΔ₀.of_le two_le_top
  have h3 : ContDiff ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ Δ₀ p) := h2.fderiv_right (by norm_num)
  have h4 : ContDiff ℝ 1 (fun x : ℝ => fderiv ℝ Δ₀ (x, arch x)) :=
    h3.comp (contDiff_id.prodMk (contDiff_arch.of_le one_le_top))
  have h5 : ContDiff ℝ 1 (fun x : ℝ => (fderiv ℝ Δ₀ (x, arch x)) (0, 1)) :=
    h4.clm_apply contDiff_const
  show ContDiff ℝ 1 (fun x : ℝ => (fderiv ℝ Δ₀ (x, arch x)) (0, 1))
  exact h5

/-- The `(0,1)`-derivative of a bump at the upper edge. -/
def edgeTop (ρ : ℝ) (k : Fin 2 × Fin 2) (x : ℝ) : ℝ :=
  fderiv ℝ (lensBump ρ k) (x, arch x) (0, 1)

/-- The `(0,1)`-derivative of a bump at the upper edge is `C^1`. -/
lemma contDiff_edgeTop (ρ : ℝ) (k : Fin 2 × Fin 2) : ContDiff ℝ 1 (edgeTop ρ k) := by
  have h2 : ContDiff ℝ 2 (lensBump ρ k) := (contDiff_lensBump ρ k).of_le two_le_top
  have h3 : ContDiff ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ (lensBump ρ k) p) :=
    h2.fderiv_right (by norm_num)
  have h4 : ContDiff ℝ 1 (fun x : ℝ => fderiv ℝ (lensBump ρ k) (x, arch x)) :=
    h3.comp (contDiff_id.prodMk (contDiff_arch.of_le one_le_top))
  have h5 : ContDiff ℝ 1 (fun x : ℝ => (fderiv ℝ (lensBump ρ k) (x, arch x)) (0, 1)) :=
    h4.clm_apply contDiff_const
  show ContDiff ℝ 1 (fun x : ℝ => (fderiv ℝ (lensBump ρ k) (x, arch x)) (0, 1))
  exact h5

/-- The one-variable derivative of `lensZeta 0 · u` at `u`. -/
lemma deriv_lensZeta_zero_top (u : ℝ) :
    deriv (fun t : ℝ => lensZeta 0 t u) u = -u := by
  have hfun : (fun t : ℝ => lensZeta 0 t u) = fun t : ℝ => u * t - t ^ 2 := by
    funext t; rw [lensZeta_zero_fun]; ring
  rw [hfun]
  change deriv ((fun t : ℝ => u * t) - fun t : ℝ => t ^ 2) u = -u
  rw [deriv_sub (by fun_prop) (by fun_prop), deriv_const_mul_id, deriv_pow_field]
  ring

/-- **The vertical derivative of the `(0,0)`-bump at the upper edge is nonzero.** -/
lemma edgeTop_zero_ne {ρ x : ℝ} (hρ : 0 < ρ) (hx : |x| < 1) :
    edgeTop ρ (0, 0) x ≠ 0 := by
  have h := (lensBump_fderiv hρ (0, 0) (x, arch x)).2
  rw [edgeTop, h, deriv_lensZeta_zero_top]
  refine mul_ne_zero (mul_ne_zero (ne_of_gt (lensChi_pos_of_abs_lt_one hρ hx)) ?_) ?_
  · rw [lensAlpha_zero_fun]
    exact ne_of_gt (by rw [abs_lt] at hx; nlinarith [hx.1, hx.2])
  · exact neg_ne_zero.mpr (ne_of_gt (arch_pos hx))

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

/-! ## The chartwise parametrisation -/

/-- The domain of the chartwise parametrisation of the upper-edge bad parameters. -/
def colDom (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (γ₂ : ℝ → M) (p : ℕ → M) (i : ℕ) : Set (PSpace n) :=
  {q | q.1 ∈ Ioo (-1 : ℝ) 1 ∧
    γ₂ (sigR q.1) ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source}

lemma isOpen_colDom (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (γ₂ : ℝ → M) (hγ₂ : Continuous γ₂) (p : ℕ → M) (i : ℕ) :
    IsOpen (colDom n γ₂ p i) := by
  have h1 : IsOpen {q : PSpace n | q.1 ∈ Set.Ioo (-1 : ℝ) 1} :=
    isOpen_Ioo.preimage continuous_fst
  have h2 : IsOpen {q : PSpace n | γ₂ (sigR q.1) ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source} :=
    (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).open_source.preimage
      (hγ₂.comp (contMDiff_sigR.continuous.comp continuous_fst))
  exact h1.inter h2

/-- The chartwise parametrisation of the upper-edge bad parameters: the `(0,0)`-block of
the parameter is recovered from the edge parameter `x`, the vector `a` parametrising the range of
the chart derivative and the three other blocks, using that `edgeTop ρ (0,0) x ≠ 0` on `(-1,1)`. -/
def colParam (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₂ : ℝ → M)
    (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (ρ : ℝ) (p : ℕ → M) (i : ℕ) :
    PSpace n → (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n)) :=
  fun q k =>
    if hk : k = (0, 0) then
      (edgeTop ρ (0, 0) q.1)⁻¹ •
        ((fderiv ℝ (chartRep2' f (p i))
              ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR q.1)))) q.2.1
          - baseDeriv Δ₀ q.1
          - ∑ k' : WIdx, edgeTop ρ k'.1 q.1 • q.2.2 k')
    else q.2.2 ⟨k, hk⟩

lemma colParam_apply_zero (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₂ : ℝ → M)
    (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (ρ : ℝ) (p : ℕ → M) (i : ℕ)
    (q : PSpace n) :
    colParam n f γ₂ Δ₀ ρ p i q (0, 0) =
      (edgeTop ρ (0, 0) q.1)⁻¹ •
        ((fderiv ℝ (chartRep2' f (p i))
              ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR q.1)))) q.2.1
          - baseDeriv Δ₀ q.1
          - ∑ k' : WIdx, edgeTop ρ k'.1 q.1 • q.2.2 k') := by
  simp only [colParam]
  rw [dif_pos trivial]

lemma colParam_apply_of_ne (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₂ : ℝ → M)
    (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (ρ : ℝ) (p : ℕ → M) (i : ℕ)
    {k : Fin 2 × Fin 2} (hk : k ≠ (0, 0)) (q : PSpace n) :
    colParam n f γ₂ Δ₀ ρ p i q k = q.2.2 ⟨k, hk⟩ := by
  simp only [colParam]
  rw [dif_neg hk]

/-- The parametrising map is `C^1` on its (open) domain. -/
lemma contDiffOn_colParam (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (γ₂ : ℝ → M)
    (hγ₂ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n)))
    (hΔ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀)
    (ρ : ℝ) (hρ : 0 < ρ) (p : ℕ → M) (i : ℕ) :
    ContDiffOn ℝ 1 (colParam n f γ₂ Δ₀ ρ p i) (colDom n γ₂ p i) := by
  have hfst : ContDiffOn ℝ 1 (fun q : PSpace n => q.1) (colDom n γ₂ p i) :=
    contDiff_fst.contDiffOn.mono (Set.subset_univ _)
  have hsw : ContDiffOn ℝ 1 (fun q : PSpace n => q.2.2) (colDom n γ₂ p i) :=
    (contDiff_snd.comp contDiff_snd).contDiffOn.mono (Set.subset_univ _)
  have hsa : ContDiffOn ℝ 1 (fun q : PSpace n => q.2.1) (colDom n γ₂ p i) :=
    (contDiff_fst.comp contDiff_snd).contDiffOn.mono (Set.subset_univ _)
  have hchart : ContDiffOn ℝ 1
      (fun q : PSpace n => (chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR q.1)))
      (colDom n γ₂ p i) :=
    ((contDiffOn_chartAt_comp_sigR hγ₂ (p i)).of_le one_le_top).comp hfst (fun q hq => hq.2)
  have hA : ContDiffOn ℝ 1
      (fun q : PSpace n => fderiv ℝ (chartRep2' f (p i))
        ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR q.1))))
      (colDom n γ₂ p i) :=
    (contDiffOn_fderiv_chartRep2' f hf (p i)).comp hchart
      (fun q hq => (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).map_source hq.2)
  have hAa : ContDiffOn ℝ 1
      (fun q : PSpace n => (fderiv ℝ (chartRep2' f (p i))
        ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR q.1)))) q.2.1)
      (colDom n γ₂ p i) := hA.clm_apply hsa
  have hb : ContDiffOn ℝ 1 (fun q : PSpace n => baseDeriv Δ₀ q.1) (colDom n γ₂ p i) :=
    (contDiff_baseDeriv hΔ₀).contDiffOn.comp (t := Set.univ) hfst (fun _ _ => Set.mem_univ _)
  have hS : ContDiffOn ℝ 1
      (fun q : PSpace n => ∑ k' : WIdx, edgeTop ρ k'.1 q.1 • q.2.2 k')
      (colDom n γ₂ p i) := by
    refine ContDiffOn.sum (fun k' _ => ?_)
    have h1 : ContDiffOn ℝ 1 (fun q : PSpace n => edgeTop ρ k'.1 q.1) (colDom n γ₂ p i) :=
      (contDiff_edgeTop ρ k'.1).contDiffOn.comp (t := Set.univ) hfst (fun _ _ => Set.mem_univ _)
    have h2 : ContDiffOn ℝ 1 (fun q : PSpace n => q.2.2 k') (colDom n γ₂ p i) := by
      refine ((ContinuousLinearMap.proj (R := ℝ) k').contDiff.comp_contDiffOn hsw).congr
        (fun q hq => ?_)
      rw [Function.comp_apply, ContinuousLinearMap.proj_apply]
    exact h1.smul h2
  have hInv : ContDiffOn ℝ 1 (fun q : PSpace n => (edgeTop ρ (0, 0) q.1)⁻¹)
      (colDom n γ₂ p i) := by
    refine ContDiffOn.inv ?_ ?_
    · exact (contDiff_edgeTop ρ (0, 0)).contDiffOn.comp (t := Set.univ) hfst
        (fun _ _ => Set.mem_univ _)
    · intro q hq
      exact edgeTop_zero_ne hρ (abs_lt.mpr ⟨hq.1.1, hq.1.2⟩)
  rw [contDiffOn_pi]
  intro k
  by_cases hk : k = (0, 0)
  · subst hk
    rw [show (fun q : PSpace n => colParam n f γ₂ Δ₀ ρ p i q (0, 0)) =
        (fun q : PSpace n => (edgeTop ρ (0, 0) q.1)⁻¹ •
          ((fderiv ℝ (chartRep2' f (p i))
              ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR q.1)))) q.2.1
            - baseDeriv Δ₀ q.1
            - ∑ k' : WIdx, edgeTop ρ k'.1 q.1 • q.2.2 k'))
        from funext (fun q => colParam_apply_zero n f γ₂ Δ₀ ρ p i q)]
    exact hInv.smul ((hAa.sub hb).sub hS)
  · rw [show (fun q : PSpace n => colParam n f γ₂ Δ₀ ρ p i q k) =
        (fun q : PSpace n => q.2.2 ⟨k, hk⟩)
        from funext (fun q => colParam_apply_of_ne n f γ₂ Δ₀ ρ p i hk q)]
    refine ((ContinuousLinearMap.proj (R := ℝ) ⟨k, hk⟩).contDiff.comp_contDiffOn hsw).congr
      (fun q hq => ?_)
    rw [Function.comp_apply, ContinuousLinearMap.proj_apply]

/-! ## The derivative of the perturbed map in the vertical direction -/

/-- `lensPert ρ v` is smooth. -/
lemma contDiff_lensPert (n : ℕ) (ρ : ℝ)
    (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lensPert ρ v) := by
  rw [show lensPert ρ v = (fun p : ℝ × ℝ => ∑ k : Fin 2 × Fin 2, lensBump ρ k p • v k)
    from rfl]
  exact ContDiff.sum (s := Finset.univ) fun k _ => (contDiff_lensBump ρ k).smul_const (v k)

/-- The derivative of `lensPert ρ v` in the direction `u`. -/
lemma fderiv_lensPert_apply (n : ℕ) (ρ : ℝ)
    (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (p u : ℝ × ℝ) :
    fderiv ℝ (lensPert ρ v) p u
      = ∑ k : Fin 2 × Fin 2, (fderiv ℝ (lensBump ρ k) p u) • v k := by
  rw [show lensPert ρ v = (fun p : ℝ × ℝ => ∑ k : Fin 2 × Fin 2, lensBump ρ k p • v k)
    from rfl]
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun k p => lensBump ρ k p • v k)
    (fun k _ => ((contDiff_lensBump ρ k).contDiffAt.differentiableAt (by simp)).smul_const
      (v k))]
  rw [sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fderiv_smul_const ((contDiff_lensBump ρ k).contDiffAt.differentiableAt (by simp)) (v k)]
  rfl

/-- **The derivative of the perturbed map** in the direction `u`. -/
lemma fderiv_lensMap_apply {n : ℕ} {Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    (hΔ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀) (ρ : ℝ)
    (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) (p u : ℝ × ℝ) :
    fderiv ℝ (lensMap Δ₀ ρ v) p u
      = fderiv ℝ Δ₀ p u + ∑ k : Fin 2 × Fin 2, (fderiv ℝ (lensBump ρ k) p u) • v k := by
  have hfun : lensMap Δ₀ ρ v = Δ₀ + lensPert ρ v := rfl
  rw [hfun, fderiv_add (hΔ₀.contDiffAt.differentiableAt (by simp))
    ((contDiff_lensPert n ρ v).contDiffAt.differentiableAt (by simp)), add_apply,
    fderiv_lensPert_apply]

/-! ## The bad parameters are covered by the chartwise parametrisations -/

/-- **Covering.**  Every upper-edge-bad parameter arises as a value of the parametrisation of one
of the charts. -/
lemma badColTop_subset {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (γ₂ : ℝ → M)
    (hγ₂ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n)))
    (hΔ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀) (ρ : ℝ) (hρ : 0 < ρ)
    (p : ℕ → M)
    (hcov : (Set.univ : Set M) ⊆ ⋃ i, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source) :
    badColTop (n := n) f Δ₀ ρ γ₂ ⊆
      ⋃ i, colParam n f γ₂ Δ₀ ρ p i '' colDom n γ₂ p i := by
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
  · have hkey : (fderiv ℝ (chartRep2' f (p i))
        ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR x)))) a
      = baseDeriv Δ₀ x + ∑ k : Fin 2 × Fin 2, edgeTop ρ k x • v k := by
      have h2 : fderiv ℝ (lensMap Δ₀ ρ v) (x, arch x) (0, 1)
          = baseDeriv Δ₀ x + ∑ k : Fin 2 × Fin 2, edgeTop ρ k x • v k := by
        rw [fderiv_lensMap_apply hΔ₀ ρ v (x, arch x) (0, 1)]
        simp only [baseDeriv, edgeTop]
      rw [← h2, ← hz, hdec, ha]
      rfl
    funext k
    by_cases hk : k = (0, 0)
    · subst hk
      rw [colParam_apply_zero n f γ₂ Δ₀ ρ p i (x, a, wblock)]
      change (edgeTop ρ (0, 0) x)⁻¹ •
          ((fderiv ℝ (chartRep2' f (p i))
              ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR x)))) a
            - baseDeriv Δ₀ x
            - ∑ k' : WIdx, edgeTop ρ k'.1 x • wblock k')
        = v (0, 0)
      have hsum := sum_split (fun k : Fin 2 × Fin 2 => edgeTop ρ k x • v k)
      have hcalc : (fderiv ℝ (chartRep2' f (p i))
            ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) (γ₂ (sigR x)))) a
          - baseDeriv Δ₀ x
          - ∑ k' : WIdx, edgeTop ρ k'.1 x • wblock k'
        = edgeTop ρ (0, 0) x • v (0, 0) := by
        simp only [hw]
        rw [hkey, hsum]
        abel
      rw [hcalc, inv_smul_smul₀ (edgeTop_zero_ne hρ (abs_lt.mpr ⟨hx.1, hx.2⟩))]
    · rw [colParam_apply_of_ne n f γ₂ Δ₀ ρ p i hk (x, a, wblock)]

end DimHColTopAux

theorem dimH_badColTop {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (γ₂ : ℝ → M)
    (hγ₂ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n)))
    (hΔ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀)
    (ρ : ℝ) (hρ : 0 < ρ) :
    dimH (Work.Drive.PushDisc.badColTop (n := n) f Δ₀ ρ γ₂) ≤ ((7 * n + 1 : ℕ) : ENNReal) := by
  classical
  haveI : Nonempty M := ⟨γ₂ 0⟩
  obtain ⟨p, hcov⟩ := Work.Projection.exists_countable_chart_cover_general
    (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (M := M)
  calc dimH (badColTop (n := n) f Δ₀ ρ γ₂)
      ≤ dimH (⋃ i, DimHColTopAux.colParam n f γ₂ Δ₀ ρ p i ''
          DimHColTopAux.colDom n γ₂ p i) :=
        dimH_mono (DimHColTopAux.badColTop_subset f hf γ₂ hγ₂ Δ₀ hΔ₀ ρ hρ p hcov)
    _ = ⨆ i, dimH (DimHColTopAux.colParam n f γ₂ Δ₀ ρ p i ''
          DimHColTopAux.colDom n γ₂ p i) := dimH_iUnion _
    _ ≤ ((7 * n + 1 : ℕ) : ENNReal) := by
        refine iSup_le fun i => ?_
        calc dimH (DimHColTopAux.colParam n f γ₂ Δ₀ ρ p i ''
              DimHColTopAux.colDom n γ₂ p i)
            ≤ (Module.finrank ℝ (DimHColTopAux.PSpace n) : ENNReal) :=
              Work.Projection.dimH_image_le_of_contDiffOn
                (DimHColTopAux.isOpen_colDom n γ₂ hγ₂.continuous p i)
                (DimHColTopAux.contDiffOn_colParam n f hf γ₂ hγ₂ Δ₀ hΔ₀ ρ hρ p i)
                (Set.Subset.refl _)
          _ = ((7 * n + 1 : ℕ) : ENNReal) := by
              rw [DimHColTopAux.finrank_PSpace]

end

end Work.Drive.PushDisc
