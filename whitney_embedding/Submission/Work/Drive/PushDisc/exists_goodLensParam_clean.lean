import Mathlib
import Submission.Work.Drive.PushDisc.lensRegularDefs
import Submission.Work.Drive.PushDisc.exists_goodLensParam

/-!
# The lens perturbation, also avoiding the image of `f`

`Work.Drive.PushDisc.exists_goodLensParam` produces a perturbation `v` of the base map `Δ₀` on the
lens such that `lensMap Δ₀ ρ v` is immersive on the (closed) lens, injective on it, and transverse
to the two arcs along the two edges of the lens.  The "clean" form proved here adds a fourth
requirement:

    ∀ p ∈ lensOpen, ∀ z : M, lensMap Δ₀ ρ v p ≠ f z,

i.e. the perturbed lens avoids the *whole* image of `f`, not only the two edges.  This is the
condition under which the Whitney disc built from the lens is genuinely disjoint from the given
immersion `f` (the lens is pushed off to one side).

The extra bad parameter set is

    badMeet f Δ₀ ρ = {v | ∃ p ∈ lensOpen, ∃ z : M, lensMap Δ₀ ρ v p = f z}.

For a chart `c : M` of the manifold we parametrise `badMeet` by the source

    MSrc n = (ℝ × ℝ) × ℝⁿ × ({k : Fin 2 × Fin 2 // k ≠ (0,0)} → ℝ^{2n}),

of real dimension `2 + n + 3 · 2n = 7n + 2`: the first factor is the point `p ∈ lensOpen`, the second
the chart coordinate `ζ` of the point `z` (so that `f z = chartRep2' f c ζ`), and the last the three
free blocks of `v`.  The `(0,0)`-block is then *solved* from the defining equation

    Δ₀ p + Σ_k lensBump ρ k p • v k = f z,

using that `lensBump ρ (0,0) p ≠ 0` for `p ∈ lensOpen` (`lensBump_zero_zero_pos`).  Hence
`badMeet` is the countable union of the images of `C¹` maps on sources of dimension `7n + 2`, so
`dimH (badMeet f Δ₀ ρ) ≤ 7n + 2`.

Together with the bounds `6n + 4 ≤ 7n + 2` and `7n + 1 ≤ 7n + 2` for the immersion-, injectivity-
and collar-bad sets, the union of all bad parameters has Hausdorff dimension `≤ 7n + 2 < 8n =
finrank ℝ (Prm n)` because `n ≥ 3`.  Its complement is therefore dense, and meets the open ball of
radius `r`, giving the required `v`.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff ENNReal
open Set Metric MeasureTheory Topology Filter

noncomputable section

/-- The parameters for which the perturbed lens meets the image of `f` on the *open* lens. -/
def badMeet {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (ρ : ℝ) :
    Set ((Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) :=
  {v | ∃ p ∈ lensOpen, ∃ z : M, lensMap Δ₀ ρ v p = f z}

namespace LensCleanAux

/-- The bump indices different from `(0,0)`. -/
abbrev WIdx : Type := {k : Fin 2 × Fin 2 // k ≠ (0, 0)}

/-- The source of the chartwise parametrisation of `badMeet`: the point `p ∈ lensOpen`, the chart
coordinate `ζ` of the point `z` and the three bump blocks other than `(0,0)`. -/
abbrev MSrc (n : ℕ) : Type :=
  (ℝ × ℝ) × EuclideanSpace ℝ (Fin n) × (WIdx → EuclideanSpace ℝ (Fin (2 * n)))

lemma card_widx : Fintype.card WIdx = 3 := by
  rw [Fintype.card_subtype]; decide

lemma finrank_fun_widx (n : ℕ) :
    Module.finrank ℝ (WIdx → EuclideanSpace ℝ (Fin (2 * n))) = 6 * n := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, card_widx,
    finrank_euclideanSpace_fin]
  simp only [nsmul_eq_mul]
  ring

/-- The finrank of the parametrising space is `7 n + 2`. -/
lemma finrank_msrc (n : ℕ) : Module.finrank ℝ (MSrc n) = 7 * n + 2 := by
  show Module.finrank ℝ ((ℝ × ℝ) × EuclideanSpace ℝ (Fin n) ×
    (WIdx → EuclideanSpace ℝ (Fin (2 * n)))) = 7 * n + 2
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, Module.finrank_self,
    finrank_euclideanSpace_fin, finrank_fun_widx]
  ring

/-- The sum over the four indices splits into the three free blocks and the `(0,0)`-block. -/
lemma sum_split {n : ℕ} (g : Fin 2 × Fin 2 → EuclideanSpace ℝ (Fin (2 * n))) :
    (∑ k : Fin 2 × Fin 2, g k) = (∑ k' : WIdx, g k'.1) + g (0, 0) := by
  have h : (∑ k ∈ Finset.univ.erase (0, 0), g k) = ∑ k' : WIdx, g k'.1 :=
    Finset.sum_subtype _ (fun k => by simp [Finset.mem_erase]) g
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0, 0)), h]

/-- The domain of the chartwise parametrisation: `p ∈ lensOpen` and `ζ` in the target of the
chart at `c`. -/
def meetDom (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (c : M) : Set (MSrc n) :=
  {q | q.1 ∈ lensOpen ∧ q.2.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) c).target}

/-- The chartwise parametrisation of `badMeet`: the `(0,0)`-block of the parameter is recovered
from `p`, the chart coordinate `ζ` of `z` and the three other blocks, using that
`lensBump ρ (0,0) p ≠ 0` on `lensOpen`. -/
def meetParam {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (c : M)
    (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (ρ : ℝ) :
    MSrc n → (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n)) :=
  fun q k => if hk : k = (0, 0) then
      (lensBump ρ (0, 0) q.1)⁻¹ •
        (DimHColBotAux.chartRep2' f c q.2.1 - Δ₀ q.1
          - ∑ k' : WIdx, lensBump ρ k'.1 q.1 • q.2.2 k')
    else q.2.2 ⟨k, hk⟩

lemma meetParam_apply_zero {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (c : M)
    (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (ρ : ℝ) (q : MSrc n) :
    meetParam f c Δ₀ ρ q (0, 0) =
      (lensBump ρ (0, 0) q.1)⁻¹ •
        (DimHColBotAux.chartRep2' f c q.2.1 - Δ₀ q.1
          - ∑ k' : WIdx, lensBump ρ k'.1 q.1 • q.2.2 k') := by
  simp only [meetParam]
  rw [dif_pos trivial]

lemma meetParam_apply_of_ne {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (c : M)
    (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (ρ : ℝ) {k : Fin 2 × Fin 2}
    (hk : k ≠ (0, 0)) (q : MSrc n) :
    meetParam f c Δ₀ ρ q k = q.2.2 ⟨k, hk⟩ := by
  simp only [meetParam]
  rw [dif_neg hk]

lemma isOpen_lensOpen : IsOpen lensOpen := by
  have h1 : IsOpen {p : ℝ × ℝ | |p.1| < (1 : ℝ)} :=
    isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  have h2 : IsOpen {p : ℝ × ℝ | (0 : ℝ) < p.2} := isOpen_lt continuous_const continuous_snd
  have h3 : IsOpen {p : ℝ × ℝ | p.2 < arch p.1} :=
    isOpen_lt continuous_snd (contDiff_arch.continuous.comp continuous_fst)
  have hset : lensOpen = {p : ℝ × ℝ | |p.1| < (1 : ℝ)} ∩ {p : ℝ × ℝ | (0 : ℝ) < p.2}
      ∩ {p : ℝ × ℝ | p.2 < arch p.1} := by
    ext p; simp only [lensOpen, Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
  rw [hset]
  exact (h1.inter h2).inter h3

lemma isOpen_meetDom (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (c : M) : IsOpen (meetDom (n := n) c) := by
  have h1 : IsOpen {q : MSrc n | q.1 ∈ lensOpen} := isOpen_lensOpen.preimage continuous_fst
  have h2 : IsOpen {q : MSrc n | q.2.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) c).target} :=
    (chartAt (EuclideanSpace ℝ (Fin n)) c).open_target.preimage
      (continuous_fst.comp continuous_snd)
  exact h1.inter h2

/-- The parametrising map is `C¹` on its (open) domain. -/
lemma contDiffOn_meetParam {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n)))
    (hΔ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀)
    (ρ : ℝ) (hρ : 0 < ρ) (c : M) :
    ContDiffOn ℝ 1 (meetParam f c Δ₀ ρ) (meetDom (n := n) c) := by
  have hfst : ContDiffOn ℝ 1 (fun q : MSrc n => q.1) (meetDom (n := n) c) :=
    contDiff_fst.contDiffOn.mono (Set.subset_univ _)
  have hsw : ContDiffOn ℝ 1 (fun q : MSrc n => q.2.2) (meetDom (n := n) c) :=
    (contDiff_snd.comp contDiff_snd).contDiffOn.mono (Set.subset_univ _)
  have hzeta : ContDiffOn ℝ 1 (fun q : MSrc n => q.2.1) (meetDom (n := n) c) :=
    (contDiff_fst.comp contDiff_snd).contDiffOn.mono (Set.subset_univ _)
  have hchart : ContDiffOn ℝ 1
      (fun q : MSrc n => DimHColBotAux.chartRep2' f c q.2.1) (meetDom (n := n) c) :=
    ((DimHColBotAux.contDiffOn_chartRep2' f hf c).of_le DimHColBotAux.one_le_top).comp
      hzeta (fun q hq => hq.2)
  have hbase : ContDiffOn ℝ 1 (fun q : MSrc n => Δ₀ q.1) (meetDom (n := n) c) :=
    (hΔ₀.of_le DimHColBotAux.one_le_top).comp_contDiffOn hfst
  have hS : ContDiffOn ℝ 1
      (fun q : MSrc n => ∑ k' : WIdx, lensBump ρ k'.1 q.1 • q.2.2 k')
      (meetDom (n := n) c) := by
    refine ContDiffOn.sum (fun k' _ => ?_)
    have h1 : ContDiffOn ℝ 1 (fun q : MSrc n => lensBump ρ k'.1 q.1) (meetDom (n := n) c) :=
      ((contDiff_lensBump ρ k'.1).of_le DimHColBotAux.one_le_top).comp_contDiffOn hfst
    have h2 : ContDiffOn ℝ 1 (fun q : MSrc n => q.2.2 k') (meetDom (n := n) c) := by
      refine ((ContinuousLinearMap.proj (R := ℝ) k').contDiff.comp_contDiffOn hsw).congr
        (fun q hq => ?_)
      rw [Function.comp_apply, ContinuousLinearMap.proj_apply]
    exact h1.smul h2
  have hInv : ContDiffOn ℝ 1 (fun q : MSrc n => (lensBump ρ (0, 0) q.1)⁻¹)
      (meetDom (n := n) c) := by
    refine ContDiffOn.inv ?_ ?_
    · exact ((contDiff_lensBump ρ (0, 0)).of_le DimHColBotAux.one_le_top).comp_contDiffOn hfst
    · intro q hq
      exact ne_of_gt (lensBump_zero_zero_pos hρ hq.1)
  rw [contDiffOn_pi]
  intro k
  by_cases hk : k = (0, 0)
  · subst hk
    rw [show (fun q : MSrc n => meetParam f c Δ₀ ρ q (0, 0)) =
        (fun q : MSrc n => (lensBump ρ (0, 0) q.1)⁻¹ •
          (DimHColBotAux.chartRep2' f c q.2.1 - Δ₀ q.1
            - ∑ k' : WIdx, lensBump ρ k'.1 q.1 • q.2.2 k'))
        from funext (fun q => meetParam_apply_zero f c Δ₀ ρ q)]
    exact hInv.smul ((hchart.sub hbase).sub hS)
  · rw [show (fun q : MSrc n => meetParam f c Δ₀ ρ q k) =
        (fun q : MSrc n => q.2.2 ⟨k, hk⟩)
        from funext (fun q => meetParam_apply_of_ne f c Δ₀ ρ hk q)]
    refine ((ContinuousLinearMap.proj (R := ℝ) ⟨k, hk⟩).contDiff.comp_contDiffOn hsw).congr
      (fun q hq => ?_)
    rw [Function.comp_apply, ContinuousLinearMap.proj_apply]

/-- **Covering.**  Every parameter for which the perturbed lens meets the image of `f` arises as a
value of the parametrisation of one of the charts. -/
lemma badMeet_subset {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (ρ : ℝ) (hρ : 0 < ρ) (p : ℕ → M)
    (hcov : (Set.univ : Set M) ⊆ ⋃ i, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source) :
    badMeet f Δ₀ ρ ⊆ ⋃ i, meetParam f (p i) Δ₀ ρ '' meetDom (n := n) (p i) := by
  rintro v ⟨q, hq, z, hz⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ z))
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  refine ⟨(q, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)) z, fun k' => v k'.1), ?_, ?_⟩
  · exact ⟨hq, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).map_source hi⟩
  · have hcz : DimHColBotAux.chartRep2' f (p i)
        ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) z) = f z := by
      show f ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)).symm
        ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) z)) = f z
      rw [(chartAt (EuclideanSpace ℝ (Fin n)) (p i)).left_inv hi]
    funext k
    by_cases hk : k = (0, 0)
    · subst hk
      rw [meetParam_apply_zero]
      have hL : Δ₀ q + (∑ k : Fin 2 × Fin 2, lensBump ρ k q • v k) = f z := by
        have h := hz
        rw [show lensMap Δ₀ ρ v q = Δ₀ q + ∑ k : Fin 2 × Fin 2, lensBump ρ k q • v k
          from rfl] at h
        exact h
      have hkey := sum_split (fun k : Fin 2 × Fin 2 => lensBump ρ k q • v k)
      have hcalc : DimHColBotAux.chartRep2' f (p i)
            ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) z) - Δ₀ q
          - ∑ k' : WIdx, lensBump ρ k'.1 q • v k'.1 = lensBump ρ (0, 0) q • v (0, 0) := by
        rw [hcz, ← hL, hkey]; abel
      rw [hcalc, inv_smul_smul₀ (ne_of_gt (lensBump_zero_zero_pos hρ hq))]
    · rw [meetParam_apply_of_ne f (p i) Δ₀ ρ hk
        (q, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)) z, fun k' => v k'.1)]

end LensCleanAux

open LensCleanAux

/-- **The Hausdorff dimension of the "lens meets `f(M)`" bad parameters.**  It is at most
`7 n + 2`, the dimension of the chartwise parametrising space. -/
theorem dimH_badMeet_le {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [Nonempty M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n)))
    (hΔ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀) (ρ : ℝ) (hρ : 0 < ρ) :
    dimH (badMeet f Δ₀ ρ) ≤ ((7 * n + 2 : ℕ) : ENNReal) := by
  classical
  obtain ⟨p, hcov⟩ := Work.Projection.exists_countable_chart_cover_general
    (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (M := M)
  calc dimH (badMeet f Δ₀ ρ)
      ≤ dimH (⋃ i, meetParam f (p i) Δ₀ ρ '' meetDom (n := n) (p i)) :=
        dimH_mono (badMeet_subset f Δ₀ ρ hρ p hcov)
    _ = ⨆ i, dimH (meetParam f (p i) Δ₀ ρ '' meetDom (n := n) (p i)) := dimH_iUnion _
    _ ≤ ((7 * n + 2 : ℕ) : ENNReal) := by
        refine iSup_le fun i => ?_
        calc dimH (meetParam f (p i) Δ₀ ρ '' meetDom (n := n) (p i))
            ≤ (Module.finrank ℝ (MSrc n) : ENNReal) :=
              Work.Projection.dimH_image_le_of_contDiffOn
                (isOpen_meetDom n (p i)) (contDiffOn_meetParam f hf Δ₀ hΔ₀ ρ hρ (p i))
                (Set.Subset.refl _)
          _ = ((7 * n + 2 : ℕ) : ENNReal) := by rw [finrank_msrc]

theorem exists_goodLensParam_clean {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (γ₁ γ₂ : ℝ → M)
    (hγ₁ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (ρ : ℝ) (hρ : 0 < ρ)
    (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (hΔ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀)
    (hbaseInj : ∀ p ∈ lens, ∀ q ∈ lens, p ≠ q →
      (∀ k : Fin 2 × Fin 2, lensBump ρ k p = lensBump ρ k q) → Δ₀ p ≠ Δ₀ q)
    (hbaseImm : ∀ p ∈ lens, ∀ UW : ℝ × ℝ, UW ≠ 0 →
      (∀ k : Fin 2 × Fin 2,
        UW.1 * fderiv ℝ (lensBump ρ k) p (1, 0) + UW.2 * fderiv ℝ (lensBump ρ k) p (0, 1) = 0) →
      UW.1 • (fderiv ℝ Δ₀ p) (1, 0) + UW.2 • (fderiv ℝ Δ₀ p) (0, 1) ≠ 0)
    (r : ℝ) (hr : 0 < r) :
    ∃ v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n)),
      (∀ k : Fin 2 × Fin 2, ‖v k‖ < r) ∧
      (∀ p ∈ lens, Function.Injective (fderiv ℝ (lensMap Δ₀ ρ v) p)) ∧
      Set.InjOn (lensMap Δ₀ ρ v) lens ∧
      (∀ p ∈ lensOpen, ∀ z : M, lensMap Δ₀ ρ v p ≠ f z) ∧
      (∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        fderiv ℝ (lensMap Δ₀ ρ v) (x, 0) (0, 1) ∉
          (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f (γ₁ (Work.Drive.Whitney.sigR x))).range) ∧
      (∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        fderiv ℝ (lensMap Δ₀ ρ v) (x, arch x) (0, 1) ∉
          (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f (γ₂ (Work.Drive.Whitney.sigR x))).range) := by
  have _hM : Nonempty M := ⟨γ₁ 0⟩
  -- the five bad parameter sets
  have h1 : dimH (badImm Δ₀ ρ) ≤ ((6 * n + 4 : ℕ) : ENNReal) := dimH_badImm_le hbaseImm hΔ₀
  have h2 : dimH (badInj Δ₀ ρ) ≤ ((6 * n + 4 : ℕ) : ENNReal) := dimH_badInj_le hbaseInj hΔ₀
  have h3 : dimH (badColBot f Δ₀ ρ γ₁) ≤ ((7 * n + 1 : ℕ) : ENNReal) :=
    dimH_badColBot f hf γ₁ hγ₁ Δ₀ hΔ₀ ρ hρ
  have h4 : dimH (badColTop f Δ₀ ρ γ₂) ≤ ((7 * n + 1 : ℕ) : ENNReal) :=
    dimH_badColTop f hf γ₂ hγ₂ Δ₀ hΔ₀ ρ hρ
  have h5 : dimH (badMeet f Δ₀ ρ) ≤ ((7 * n + 2 : ℕ) : ENNReal) :=
    dimH_badMeet_le f hf Δ₀ hΔ₀ ρ hρ
  set Bad : Set (Prm n) :=
    badImm Δ₀ ρ ∪ badInj Δ₀ ρ ∪ badColBot f Δ₀ ρ γ₁ ∪ badColTop f Δ₀ ρ γ₂
      ∪ badMeet f Δ₀ ρ with hBad
  have h64 : ((6 * n + 4 : ℕ) : ENNReal) ≤ ((7 * n + 2 : ℕ) : ENNReal) := by
    rw [Nat.cast_le]; omega
  have h71 : ((7 * n + 1 : ℕ) : ENNReal) ≤ ((7 * n + 2 : ℕ) : ENNReal) := by
    rw [Nat.cast_le]; omega
  have hdim : dimH Bad ≤ ((7 * n + 2 : ℕ) : ENNReal) := by
    rw [hBad]
    rw [dimH_union, dimH_union, dimH_union, dimH_union]
    exact max_le (max_le (max_le (max_le (h1.trans h64) (h2.trans h64)) (h3.trans h71))
      (h4.trans h71)) h5
  have hlt : dimH Bad < (Module.finrank ℝ (Prm n) : ENNReal) := by
    rw [finrank_prm]
    exact lt_of_le_of_lt hdim (by rw [Nat.cast_lt]; omega)
  have hUopen : IsOpen {v : Prm n | ∀ k : Fin 2 × Fin 2, ‖v k‖ < r} := by
    rw [show {v : Prm n | ∀ k : Fin 2 × Fin 2, ‖v k‖ < r}
        = ⋂ k : Fin 2 × Fin 2, {v : Prm n | ‖v k‖ < r} from by
      ext v; simp]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_lt (continuous_norm.comp (continuous_apply k)) continuous_const
  have hUne : ({v : Prm n | ∀ k : Fin 2 × Fin 2, ‖v k‖ < r}).Nonempty :=
    ⟨0, fun k => by simpa using hr⟩
  obtain ⟨v, hvBad, hvball⟩ :=
    (dense_compl_of_dimH_lt_finrank hlt).exists_mem_open hUopen hUne
  have hv1 : v ∉ badImm Δ₀ ρ :=
    fun h => hvBad (by rw [hBad]; exact Or.inl (Or.inl (Or.inl (Or.inl h))))
  have hv2 : v ∉ badInj Δ₀ ρ :=
    fun h => hvBad (by rw [hBad]; exact Or.inl (Or.inl (Or.inl (Or.inr h))))
  have hv3 : v ∉ badColBot f Δ₀ ρ γ₁ :=
    fun h => hvBad (by rw [hBad]; exact Or.inl (Or.inl (Or.inr h)))
  have hv4 : v ∉ badColTop f Δ₀ ρ γ₂ :=
    fun h => hvBad (by rw [hBad]; exact Or.inl (Or.inr h))
  have hv5 : v ∉ badMeet f Δ₀ ρ := fun h => hvBad (by rw [hBad]; exact Or.inr h)
  refine ⟨v, hvball, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    by_contra hinj
    exact hv1 ⟨p, hp, hinj⟩
  · intro p hp q hq hpq
    by_contra hne
    exact hv2 ⟨p, hp, q, hq, hne, hpq⟩
  · intro p hp z hz
    exact hv5 ⟨p, hp, z, hz⟩
  · intro x hx
    by_contra hmem
    exact hv3 ⟨x, hx, hmem⟩
  · intro x hx
    by_contra hmem
    exact hv4 ⟨x, hx, hmem⟩

end

end Work.Drive.PushDisc
