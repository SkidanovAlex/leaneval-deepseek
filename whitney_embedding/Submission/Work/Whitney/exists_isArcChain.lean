import Mathlib
import Submission.Work.Whitney.ArcFraming
import Submission.Work.Whitney.fderiv_transition_det_ne_zero

/-!
# Arc chains always exist

Given a continuous arc `γ : ℝ → M` in a smooth `n`-manifold `M`, and a smooth chart `c` with
`γ 1 ∈ c.source`, there is a smooth chart `c₀` with `γ 0 ∈ c₀.source` together with a *positive
chain of charts along `γ`* from `c₀` to `c` (`Work.Whitney.IsArcChain`).

The proof has three steps.

* `exists_arc_cover`: cover the compact arc `γ '' [0,1]` by finitely many chart sources (Lebesgue
  number of the pullback cover of `[0,1]`), producing a partition `0 = t 0 ≤ ⋯ ≤ t K = 1` and,
  for each piece, a smooth chart containing it.
* `exists_posTransitionAt_flip`: if `f, g` are smooth charts and `y` lies in both sources, then
  either the transition `f → g` is already positive at `f y`, or we may post-compose `f` with a
  linear reflection of `EuclideanSpace ℝ (Fin n)` of determinant `-1`; the source is unchanged and
  the transition becomes positive.  (For `n = 0` every transition is already positive.)
* `arcChain_aux`: running the previous step from the far end of the partition towards its start,
  each chart of the cover is replaced by one positively related to its successor.

The determinant of the transition is non-zero by
`Work.Whitney.fderiv_transition_det_ne_zero`.
-/

namespace Work.Whitney

open scoped Manifold ContDiff RealInnerProductSpace
open Topology ChartedSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The charts of the atlas are smooth charts. -/
theorem isSmoothChart_chartAt (x : M) :
    IsSmoothChart (chartAt (EuclideanSpace ℝ (Fin n)) x) :=
  ⟨contMDiffOn_chart, contMDiffOn_chart_symm⟩

/-- **The arc is covered by finitely many chart sources.**  There are `K ≥ 1`, a monotone
partition `t : ℕ → ℝ` of `[0,1]` with `t 0 = 0` and `t K = 1`, and smooth charts `e j` (for
`j ≤ K`) such that `e K = c` and each piece `γ '' [t j, t (j+1)]` (`j < K`) lies in the source of
`e j`. -/
theorem exists_arc_cover (γ : ℝ → M) (hγ : Continuous γ)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hc : IsSmoothChart c) :
    ∃ (K : ℕ) (_ : 0 < K) (t : ℕ → ℝ)
      (e : ℕ → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
      t 0 = 0 ∧ t K = 1 ∧ Monotone t ∧ e K = c ∧
      (∀ j ≤ K, IsSmoothChart (e j)) ∧
      (∀ j < K, γ '' Set.Icc (t j) (t (j + 1)) ⊆ (e j).source) := by
  classical
  have hopen : ∀ x : M, IsOpen (γ ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :=
    fun x => (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.preimage hγ
  have hcover : Set.Icc (0:ℝ) 1 ⊆ ⋃ x : M, γ ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
    intro s _
    exact Set.mem_iUnion.mpr ⟨γ s, mem_chart_source (EuclideanSpace ℝ (Fin n)) (γ s)⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric (s := Set.Icc (0:ℝ) 1)
      (c := fun x : M => γ ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
      isCompact_Icc hopen hcover
  obtain ⟨K, hKδ⟩ := exists_nat_gt (1/δ)
  have hKposR : (0:ℝ) < K := lt_trans (by positivity) hKδ
  have hKpos : 0 < K := by exact_mod_cast hKposR
  have hKne : (K:ℝ) ≠ 0 := ne_of_gt hKposR
  have hKinv : (1:ℝ)/(K:ℝ) < δ := by
    have h := (div_lt_iff₀ hδpos).mp hKδ
    rw [div_lt_iff₀ hKposR]
    linarith [h]
  have hwit : ∀ j : ℕ, j < K → ∃ x : M,
      Metric.ball ((j:ℝ)/(K:ℝ)) δ ⊆ γ ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
    intro j hj
    refine hδ _ ⟨by positivity, ?_⟩
    rw [div_le_one hKposR]
    exact_mod_cast Nat.le_of_lt hj
  let t : ℕ → ℝ := fun j => min ((j:ℝ)/(K:ℝ)) 1
  let e : ℕ → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    fun j => if h : j < K then chartAt (EuclideanSpace ℝ (Fin n)) (Classical.choose (hwit j h)) else c
  refine ⟨K, hKpos, t, e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show min (((0:ℕ):ℝ)/(K:ℝ)) 1 = 0
    simp
  · show min ((K:ℝ)/(K:ℝ)) 1 = 1
    rw [div_self hKne, min_self]
  · intro a b hab
    exact min_le_min (div_le_div_of_nonneg_right (Nat.cast_le.mpr hab) (le_of_lt hKposR)) le_rfl
  · show (if h : K < K then chartAt (EuclideanSpace ℝ (Fin n)) (Classical.choose (hwit K h)) else c) = c
    rw [dif_neg (lt_irrefl K)]
  · intro j _
    show IsSmoothChart (if h : j < K then chartAt (EuclideanSpace ℝ (Fin n)) (Classical.choose (hwit j h)) else c)
    by_cases h : j < K
    · rw [dif_pos h]
      exact isSmoothChart_chartAt _
    · rw [dif_neg h]
      exact hc
  · intro j hj
    have htj : t j = (j:ℝ)/(K:ℝ) := by
      show min ((j:ℝ)/(K:ℝ)) 1 = (j:ℝ)/(K:ℝ)
      exact min_eq_left (le_of_lt ((div_lt_one hKposR).mpr (Nat.cast_lt.mpr hj)))
    have htjs : t (j+1) = ((j:ℝ)+1)/(K:ℝ) := by
      show min (((j+1:ℕ):ℝ)/(K:ℝ)) 1 = _
      rw [Nat.cast_add, Nat.cast_one]
      exact min_eq_left ((div_le_one hKposR).mpr (by exact_mod_cast Nat.succ_le_of_lt hj))
    rw [htj, htjs]
    have hej : e j = chartAt (EuclideanSpace ℝ (Fin n)) (Classical.choose (hwit j hj)) := dif_pos hj
    rw [hej, Set.image_subset_iff]
    refine Set.Subset.trans ?_ (Classical.choose_spec (hwit j hj))
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
    have h2 : s - (j:ℝ)/(K:ℝ) ≤ 1/(K:ℝ) := by
      have h3 := hs.2
      rw [add_div] at h3
      linarith
    exact lt_of_le_of_lt h2 hKinv

/-- **A chart can be flipped to make its transition to a fixed chart positive.**  Given smooth
charts `f, g` and a point `y` in both sources, there is a smooth chart `f'` with the same source
as `f` whose transition to `g` at `y` is positive. -/
theorem exists_posTransitionAt_flip
    (f g : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (y : M)
    (hf : IsSmoothChart f) (hg : IsSmoothChart g)
    (hfy : y ∈ f.source) (hgy : y ∈ g.source) :
    ∃ f' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      IsSmoothChart f' ∧ f'.source = f.source ∧ PosTransitionAt f' g y := by
  classical
  by_cases hn : n = 0
  · subst hn
    refine ⟨f, hf, rfl, ?_⟩
    show (0:ℝ) < (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 0) => g (f.symm u)) (f y)).det
    rw [show (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 0) => g (f.symm u)) (f y))
          = (1 : EuclideanSpace ℝ (Fin 0) →L[ℝ] EuclideanSpace ℝ (Fin 0)) from
        ContinuousLinearMap.ext (fun u => Subsingleton.elim _ _)]
    rw [clm_det_one]
    norm_num
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hwne : (EuclideanSpace.single (⟨0, hn1⟩ : Fin n) (1:ℝ) : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
      intro h
      have hc := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v ⟨0, hn1⟩) h
      simp at hc
    let w : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (⟨0, hn1⟩ : Fin n) (1:ℝ)
    have hwne' : w ≠ 0 := hwne
    let K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := (ℝ ∙ w)ᗮ
    let R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) := K.reflection
    have hRdet : LinearMap.det (K.reflection.toLinearEquiv.toLinearMap) = -1 := by
      rw [Submodule.det_reflection]
      have h1 : Module.finrank ℝ ↥(Kᗮ) = 1 := by
        show Module.finrank ℝ ↥(((ℝ ∙ w)ᗮ)ᗮ) = 1
        rw [Submodule.orthogonal_orthogonal, finrank_span_singleton hwne']
      rw [h1]; norm_num
    by_cases hpos : PosTransitionAt f g y
    · exact ⟨f, hf, rfl, hpos⟩
    · let Roph : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
        (R.toHomeomorph).toOpenPartialHomeomorph
      let f' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) := f.trans Roph
      have hfsrc : f'.source = f.source := by
        rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
        simp
      have hftgt : f'.target = (⇑R.symm) ⁻¹' f.target := by
        rw [OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
          Homeomorph.toOpenPartialHomeomorph_symm_apply]
        simp
      have hf'val : ⇑f' = ⇑R ∘ ⇑f := by
        funext x
        rw [OpenPartialHomeomorph.coe_trans, Homeomorph.toOpenPartialHomeomorph_apply]
        rfl
      have hf'symm : ⇑f'.symm = ⇑f.symm ∘ ⇑R.symm := by
        funext u
        rw [OpenPartialHomeomorph.coe_trans_symm, Homeomorph.toOpenPartialHomeomorph_symm_apply]
        rfl
      refine ⟨f', ?_, hfsrc, ?_⟩
      · constructor
        · rw [hfsrc, hf'val]
          exact ContMDiffOn.comp (t := Set.univ)
            (R.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff.contMDiffOn)
            hf.1 (fun x _ => Set.mem_univ _)
        · rw [hftgt, hf'symm]
          exact ContMDiffOn.comp (t := f.target) hf.2
            (R.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff.contMDiffOn)
            (fun u hu => hu)
      · have hgmd : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            ((⊤:ℕ∞):WithTop ℕ∞) (fun u : EuclideanSpace ℝ (Fin n) => g (f.symm u)) (f y) := by
          have h1 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
              ((⊤:ℕ∞):WithTop ℕ∞) f.symm (f y) :=
            hf.2.contMDiffAt (f.open_target.mem_nhds (f.map_source hfy))
          have h2 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
              ((⊤:ℕ∞):WithTop ℕ∞) g (f.symm (f y)) := by
            rw [f.left_inv hfy]
            exact hg.1.contMDiffAt (g.open_source.mem_nhds hgy)
          exact h2.comp (f y) h1
        have hτdiff : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => g (f.symm u)) (f y) :=
          (contMDiffAt_iff_contDiffAt.mp hgmd).differentiableAt (by simp)
        have hne : (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => g (f.symm u)) (f y)).det ≠ 0 :=
          fderiv_transition_det_ne_zero g f y hgy hfy
            (fun z hz => hg.1.contMDiffAt (g.open_source.mem_nhds hz))
            (fun u hu => hg.2.contMDiffAt (g.open_target.mem_nhds hu))
            (fun z hz => hf.1.contMDiffAt (f.open_source.mem_nhds hz))
            (fun u hu => hf.2.contMDiffAt (f.open_target.mem_nhds hu))
        have hneg : (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => g (f.symm u)) (f y)).det < 0 :=
          lt_of_le_of_ne (le_of_not_gt hpos) hne
        have hRsymmfy : R.symm (f' y) = f y := by
          rw [show f' y = R (f y) from congrFun hf'val y, LinearIsometryEquiv.symm_apply_apply]
        have hRsdet : (R.symm.toContinuousLinearEquiv.toContinuousLinearMap).det = -1 := by
          rw [ContinuousLinearMap.det]
          rw [show (R.symm.toContinuousLinearEquiv.toContinuousLinearMap :
              EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
              = ↑(R.toLinearEquiv).symm from rfl]
          rw [LinearEquiv.det_coe_symm, hRdet]
          norm_num
        have hdR : fderiv ℝ (⇑R.symm) (f' y)
            = (R.symm.toContinuousLinearEquiv.toContinuousLinearMap) :=
          (R.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).fderiv
        have hcomp : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => g (f'.symm u)) (f' y)
            = (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => g (f.symm u)) (f y)).comp
                (R.symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
          have hfe : (fun u : EuclideanSpace ℝ (Fin n) => g (f'.symm u))
              = (fun u : EuclideanSpace ℝ (Fin n) => g (f.symm u)) ∘ (⇑R.symm) := by
            funext u
            rw [hf'symm]
            rfl
          rw [hfe]
          rw [fderiv_comp (f := ⇑R.symm) (g := fun u : EuclideanSpace ℝ (Fin n) => g (f.symm u))
            (x := f' y) (by rw [hRsymmfy]; exact hτdiff)
            ((R.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).differentiableAt)]
          rw [hRsymmfy, hdR]
        show (0:ℝ) < (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => g (f'.symm u)) (f' y)).det
        rw [hcomp, clm_det_comp, hRsdet]
        linarith

/-- Data of a positive chain of charts along `γ` from time `a` to time `1`, indexed by `ℕ` rather
than by a `Fin` type; this is the form in which the induction below goes through. -/
def ArcChainData (γ : ℝ → M) (a : ℝ) (K : ℕ) (t : ℕ → ℝ)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (c₀ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (d : ℕ → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
    IsSmoothChart c₀ ∧ d 0 = c₀ ∧ (∀ j ≤ K, IsSmoothChart (d j)) ∧
      d K = c ∧ γ a ∈ c₀.source ∧ γ 1 ∈ c.source ∧
      (∀ j < K, γ '' Set.Icc (t j) (t (j + 1)) ⊆ (d j).source) ∧
      (∀ j < K, γ (t (j + 1)) ∈ (d (j + 1)).source ∧
        PosTransitionAt (d j) (d (j + 1)) (γ (t (j + 1))))

/-- **From a cover of the arc by a positive chain of charts.**  Given a partition `t` of `[a,1]`
(`t 0 = a`, `t K = 1`, monotone) and smooth charts `e j` covering the pieces, with `e K = c`, there
are a chart `c₀` and charts `d j` such that the chain is positive at every junction.  Proved by
induction on `K`, prepending one flipped chart at a time. -/
theorem arcChain_aux
    (γ : ℝ → M) (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hγ1 : γ 1 ∈ c.source) :
    ∀ K : ℕ, 1 ≤ K → ∀ (a : ℝ) (t : ℕ → ℝ)
        (e : ℕ → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
      t 0 = a → t K = 1 → Monotone t → e K = c →
      (∀ j ≤ K, IsSmoothChart (e j)) →
      (∀ j < K, γ '' Set.Icc (t j) (t (j + 1)) ⊆ (e j).source) →
      ArcChainData γ a K t (e K) := by
  refine Nat.le_induction ?base ?step
  · intro a t e ht0 ht1 hmono he1 he hsub
    have he0sm : IsSmoothChart (e 0) := he 0 (by norm_num)
    have he1sm : IsSmoothChart (e 1) := he 1 le_rfl
    have ht01 : t 0 ≤ t 1 := hmono (by norm_num)
    have hmem0 : γ (t 1) ∈ (e 0).source :=
      (hsub 0 (by norm_num)) ⟨t 1, ⟨ht01, le_rfl⟩, rfl⟩
    have hmem1 : γ (t 1) ∈ (e 1).source := by rw [ht1, he1]; exact hγ1
    obtain ⟨c₀, hc₀sm, hc₀src, hc₀pos⟩ :=
      exists_posTransitionAt_flip (e 0) (e 1) (γ (t 1)) he0sm he1sm hmem0 hmem1
    have hd0 : (fun j => if j = 0 then c₀ else e 1) 0 = c₀ := if_pos rfl
    have hd1 : (fun j => if j = 0 then c₀ else e 1) 1 = e 1 := if_neg (by norm_num)
    refine ⟨c₀, fun j => if j = 0 then c₀ else e 1, hc₀sm, hd0, ?_, hd1, ?_,
      (by rw [← ht1]; exact hmem1), ?_, ?_⟩
    · intro j hj
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0]; exact hc₀sm
      · have hj1 : j = 1 := by omega
        rw [hj1, hd1]; exact he1sm
    · have h1 : γ (t 0) ∈ (e 0).source :=
        (hsub 0 (by norm_num)) ⟨t 0, ⟨le_rfl, ht01⟩, rfl⟩
      rw [← ht0, hc₀src]
      exact h1
    · intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [hd0, hc₀src]
      exact hsub 0 (by norm_num)
    · intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      have hd1' : (fun j => if j = 0 then c₀ else e 1) (0 + 1) = e 1 := by
        rw [show (0:ℕ) + 1 = 1 from rfl]; exact hd1
      refine ⟨?_, ?_⟩
      · rw [hd1', ht1, he1]
        exact hγ1
      · rw [hd0, hd1']
        exact hc₀pos
  · intro K hK ih a t e ht0 htK1 hmono heK1 he hsub
    obtain ⟨c₁, d', hc₁sm, hd'0, hd'sm, hd'K, hmem_a', hmem1, hd'piece, hd'pos⟩ :=
      ih (t 1) (fun j => t (j + 1)) (fun j => e (j + 1)) rfl (by simpa using htK1)
        (fun i j hij => hmono (Nat.add_le_add_right hij 1)) (by simpa using heK1)
        (fun j hj => he (j + 1) (by omega)) (fun j hj => hsub (j + 1) (by omega))
    have hmem_e0 : γ (t 1) ∈ (e 0).source :=
      (hsub 0 (by omega)) ⟨t 1, ⟨hmono (by omega), le_rfl⟩, rfl⟩
    obtain ⟨c₀, hc₀sm, hc₀src, hc₀pos⟩ :=
      exists_posTransitionAt_flip (e 0) c₁ (γ (t 1)) (he 0 (by omega)) hc₁sm hmem_e0 hmem_a'
    have hd0 : (fun j => if j = 0 then c₀ else d' (j - 1)) 0 = c₀ := if_pos rfl
    have hdne : ∀ j, j ≠ 0 →
        (fun j => if j = 0 then c₀ else d' (j - 1)) j = d' (j - 1) :=
      fun j hj => if_neg hj
    refine ⟨c₀, fun j => if j = 0 then c₀ else d' (j - 1), hc₀sm, hd0, ?_, ?_, ?_, hmem1, ?_, ?_⟩
    · intro j hj
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0]; exact hc₀sm
      · rw [hdne j (by omega)]
        exact hd'sm (j - 1) (by omega)
    · rw [hdne (K + 1) (by omega), show K + 1 - 1 = K from rfl]
      exact hd'K
    · have h1 : γ (t 0) ∈ (e 0).source :=
        (hsub 0 (by omega)) ⟨t 0, ⟨le_rfl, hmono (by omega)⟩, rfl⟩
      rw [← ht0, hc₀src]
      exact h1
    · intro j hj
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0, hd0, hc₀src]
        exact hsub 0 (by omega)
      · rw [hdne j (by omega)]
        have h := hd'piece (j - 1) (by omega)
        simp only [] at h
        have h1 : j - 1 + 1 = j := by omega
        rw [h1] at h
        exact h
    · intro j hj
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        have hd1 : (fun j => if j = 0 then c₀ else d' (j - 1)) (0 + 1) = c₁ := by
          rw [hdne (0 + 1) (by omega), show 0 + 1 - 1 = 0 from rfl, hd'0]
        refine ⟨?_, ?_⟩
        · rw [hd1]; exact hmem_a'
        · rw [hd0, hd1]
          exact hc₀pos
      · rw [hdne j (by omega), hdne (j + 1) (by omega), Nat.add_sub_cancel]
        obtain ⟨hp1, hp2⟩ := hd'pos (j - 1) (by omega)
        simp only [] at hp1 hp2
        have h1 : j - 1 + 1 = j := by omega
        rw [h1] at hp1 hp2
        exact ⟨hp1, hp2⟩

theorem exists_isArcChain {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (γ : ℝ → M) (hγ : Continuous γ)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : Work.Whitney.IsSmoothChart c) (hγ1 : γ 1 ∈ c.source) :
    ∃ c₀ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      Work.Whitney.IsSmoothChart c₀ ∧ Work.Whitney.IsArcChain γ c₀ c := by
  obtain ⟨K, hK, t, e, ht0, htK, hmono, heK, he, hsub⟩ := exists_arc_cover γ hγ c hc
  obtain ⟨c₀, d, hc₀sm, hd0, hdsm, hdK, hmem0, hmem1, hpiece, hpos⟩ :=
    arcChain_aux γ c hγ1 K hK 0 t e ht0 htK hmono heK he hsub
  refine ⟨c₀, hc₀sm, K, hK, (fun i : Fin (K + 1) => d i.val),
    (fun i : Fin (K + 1) => t i.val), ?_, ?_, ?_, hd0, ?_, hmem0, ?_, ?_, ?_, ?_⟩
  · simpa using ht0
  · simpa using htK
  · intro i j hij
    exact hmono (Fin.le_iff_val_le_val.mp hij)
  · simpa using hdK.trans heK
  · rw [← heK]; exact hmem1
  · intro i
    exact hdsm i.val (by have := i.isLt; omega)
  · intro i
    have h := hpiece i.val (by have := i.isLt; omega)
    simpa [Fin.val_castSucc, Fin.val_succ] using h
  · intro i
    have h := hpos i.val (by have := i.isLt; omega)
    simpa [Fin.val_castSucc, Fin.val_succ] using h

end Work.Whitney
