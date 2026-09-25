import Mathlib
import Submission.Work.NN.DiscRadial.ReflDefs
import Submission.Work.NN.DiscRadial.continuousOn_traceLimUnder

noncomputable section

namespace Work.NN.DiscRadial

open scoped Topology ContDiff NNReal ENNReal BigOperators
open Metric Set Filter
open Work.NN.Final

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## The reflected sum agrees with the unfolded extension where the cutoffs are `1` -/

/-- Where the cutoff arguments `-discScale i * σ` have modulus `< 1` and `σ < 0`, the unfolded
extension agrees, near the point, with the reflected sum `discUnfoldSum`. -/
lemma discUnfoldExt_eventuallyEq_discUnfoldSum {k : ℕ} {g : X × ℂ → ℂ}
    {q : (X × ℂ) × ℝ} (hq : q.2 < 0)
    (hcut : ∀ i ∈ Finset.range (k + 1), |discScale i * q.2| < 1) :
    discUnfoldExt k g =ᶠ[𝓝 q] discUnfoldSum (X := X) k g := by
  have h1 : ∀ᶠ r in 𝓝 q, r.2 < 0 :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds hq
  have h2 : ∀ᶠ r in 𝓝 q, ∀ i ∈ Finset.range (k + 1), seeleyCut (-(discScale i) * r.2) = 1 := by
    rw [eventually_all_finset]
    intro i hi
    have ht : |-(discScale i) * q.2| < 1 := by
      simpa only [neg_mul, abs_neg] using hcut i hi
    have hne : {u : ℝ | seeleyCut u = 1} ∈ 𝓝 (-(discScale i) * q.2) := by
      refine Filter.mem_of_superset
        ((isOpen_lt continuous_abs continuous_const).mem_nhds ht) ?_
      intro u hu
      exact seeleyCut_eq_one_of_abs_lt_one hu
    exact (continuous_const.mul continuous_snd).tendsto q hne
  filter_upwards [h1, h2] with r hr1 hr2
  rw [discUnfoldExt_of_neg hr1, discUnfoldSum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hr2 i hi, one_smul, reflCLM_apply]

/-! ## The iterated derivatives of the reflected sum -/

/-- On a set `S` whose points are mapped by all the reflections into the open set `Ω`, the
iterated derivatives of the reflected sum tend to the limit `Φ` of the iterated derivatives of
`discUnfold g` at `p` (a point of the hyperplane `σ = 0`). -/
theorem tendsto_iteratedFDeriv_discUnfoldSum {k m : ℕ} (hm : m ≤ k) {g : X × ℂ → ℂ}
    {Ω : Set ((X × ℂ) × ℝ)} (hΩ : IsOpen Ω)
    (hcd : ContDiffOn ℝ (k : WithTop ENat) (discUnfold g) Ω)
    {p : (X × ℂ) × ℝ} (hp0 : p.2 = 0) {S : Set ((X × ℂ) × ℝ)}
    (hS : ∀ q ∈ S, ∀ i ∈ Finset.range (k + 1), reflCLM (X := X) i q ∈ Ω)
    {Φ : ContinuousMultilinearMap ℝ (fun _ : Fin m => (X × ℂ) × ℝ) ℂ}
    (hΦ : Tendsto (fun q => iteratedFDeriv ℝ m (discUnfold g) q) (𝓝[Ω] p) (𝓝 Φ)) :
    Tendsto (fun q => iteratedFDeriv ℝ m (discUnfoldSum (X := X) k g) q) (𝓝[S] p) (𝓝 Φ) := by
  have hterm : ∀ i ∈ Finset.range (k + 1),
      Tendsto (fun q => (discWt k i) •
          (iteratedFDeriv ℝ m (discUnfold g) (reflCLM (X := X) i q)).compContinuousLinearMap
            (fun _ => reflCLM (X := X) i)) (𝓝[S] p)
        (𝓝 ((discWt k i) • Φ.compContinuousLinearMap
          (fun _ : Fin m => reflCLM (X := X) i))) := by
    intro i hi
    have hLp : reflCLM (X := X) i p = p := by
      rw [reflCLM_apply, hp0, mul_zero]
      exact Prod.ext rfl hp0.symm
    have hLi : Tendsto (reflCLM (X := X) i) (𝓝[S] p) (𝓝[Ω] p) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · exact (((reflCLM (X := X) i).continuous.tendsto' p p hLp)).mono_left
          (nhdsWithin_le_nhds (s := S))
      · exact Filter.eventually_of_mem self_mem_nhdsWithin fun q hq => hS q hq i hi
    have h1 : Tendsto (fun q => iteratedFDeriv ℝ m (discUnfold g) (reflCLM (X := X) i q))
        (𝓝[S] p) (𝓝 Φ) := hΦ.comp hLi
    have h2 : Tendsto (fun q => (iteratedFDeriv ℝ m (discUnfold g)
          (reflCLM (X := X) i q)).compContinuousLinearMap (fun _ => reflCLM (X := X) i))
        (𝓝[S] p) (𝓝 (Φ.compContinuousLinearMap (fun _ : Fin m => reflCLM (X := X) i))) :=
      (ContinuousMultilinearMap.compContinuousLinearMapL
        (𝕜 := ℝ) (fun _ : Fin m => reflCLM (X := X) i)).continuous.continuousAt.tendsto.comp h1
    exact h2.const_smul (discWt k i)
  have hmain : Tendsto (fun q => ∑ i ∈ Finset.range (k + 1), (discWt k i) •
      (iteratedFDeriv ℝ m (discUnfold g) (reflCLM (X := X) i q)).compContinuousLinearMap
        (fun _ => reflCLM (X := X) i)) (𝓝[S] p) (𝓝 Φ) := by
    have h := tendsto_finset_sum (Finset.range (k + 1)) hterm
    rwa [reflMoment (X := X) hm Φ] at h
  refine hmain.congr' ?_
  refine Filter.eventually_of_mem self_mem_nhdsWithin fun q hq => ?_
  exact (iteratedFDeriv_discUnfoldSum_eq hm hΩ hcd (hS q hq)).symm

/-! ## Uncurrying the order-`0` derivative -/

/-- The order-`0` iterated derivative is the function itself, up to the (linear isometry)
equivalence `continuousMultilinearCurryFin0`. -/
lemma tendsto_uncurry_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : E → ℂ} {l : Filter E} {Φ : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℂ}
    (h : Tendsto (fun q => iteratedFDeriv ℝ 0 U q) l (𝓝 Φ)) :
    Tendsto U l (𝓝 ((continuousMultilinearCurryFin0 ℝ E ℂ) Φ)) := by
  have hfun : (fun q => iteratedFDeriv ℝ 0 U q) =
      fun q => (continuousMultilinearCurryFin0 ℝ E ℂ).symm (U q) := by
    funext q
    rw [iteratedFDeriv_zero_eq_comp]
    rfl
  rw [hfun] at h
  have h2 : Tendsto (fun q => (continuousMultilinearCurryFin0 ℝ E ℂ)
      ((continuousMultilinearCurryFin0 ℝ E ℂ).symm (U q))) l
      (𝓝 ((continuousMultilinearCurryFin0 ℝ E ℂ) Φ)) :=
    (continuousMultilinearCurryFin0 ℝ E ℂ).continuous.continuousAt.tendsto.comp h
  have h3 : (fun q => (continuousMultilinearCurryFin0 ℝ E ℂ)
      ((continuousMultilinearCurryFin0 ℝ E ℂ).symm (U q))) = U := by
    funext q
    rw [LinearIsometryEquiv.apply_symm_apply]
  rwa [h3] at h2

/-! ## The one-sided limits of the unfolded extension at a point of the hyperplane -/

/-- The limit of the iterated derivatives of the unfolded extension from the negative side agrees
with the limit of the iterated derivatives of `discUnfold g` from the positive side. -/
lemma tendsto_iteratedFDeriv_discUnfoldExt_neg {k m : ℕ} (hm : m ≤ k) {g : X × ℂ → ℂ}
    {W : Set (X × ℂ)} (hW : IsOpen W) {ε : ℝ} (hε : 0 < ε)
    (hcd : ContDiffOn ℝ (k : WithTop ENat) (discUnfold g) (W ×ˢ Set.Ioo 0 ε))
    {y : X × ℂ} (hy : y ∈ W)
    {Φ : ContinuousMultilinearMap ℝ (fun _ : Fin m => (X × ℂ) × ℝ) ℂ}
    (hΦ : Tendsto (fun q => iteratedFDeriv ℝ m (discUnfold g) q)
        (𝓝[W ×ˢ Set.Ioo 0 ε] (y, (0 : ℝ))) (𝓝 Φ)) :
    Tendsto (fun q => iteratedFDeriv ℝ m (discUnfoldExt k g) q)
      (𝓝[{q : (X × ℂ) × ℝ | q.2 < 0}] (y, (0 : ℝ))) (𝓝 Φ) := by
  set θ : ℝ := min 1 ε / (2 * ((k : ℝ) + 2)) with hθdef
  have hθpos : 0 < θ := by
    rw [hθdef]
    exact div_pos (lt_min (by norm_num) hε) (by positivity)
  obtain ⟨r₀, hr₀pos, hr₀W⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hy)
  set r : ℝ := min r₀ θ with hrdef
  have hrpos : 0 < r := lt_min hr₀pos hθpos
  set S : Set ((X × ℂ) × ℝ) := {q | q.2 < 0} ∩ Metric.ball (y, (0 : ℝ)) r with hSdef
  have hSgood : ∀ q ∈ S, ∀ i ∈ Finset.range (k + 1),
      reflCLM (X := X) i q ∈ W ×ˢ Set.Ioo 0 ε := by
    intro q hq i hi
    have hq2 : q.2 < 0 := hq.1
    have hqy : q.1 ∈ W := by
      refine hr₀W ?_
      have h1 : dist q.1 y ≤ dist q (y, (0 : ℝ)) := by
        rw [Prod.dist_eq]; exact le_max_left _ _
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt h1 (lt_of_lt_of_le hq.2 (min_le_left _ _))
    have hσ : |q.2| < θ := by
      have h1 : |q.2| ≤ dist q (y, (0 : ℝ)) := by
        rw [Prod.dist_eq, Real.dist_eq, sub_zero]
        exact le_max_right _ _
      exact lt_of_lt_of_le (lt_of_le_of_lt h1 hq.2) (min_le_right r₀ θ)
    exact reflCLM_mem_of_abs_snd_lt (X := X) hε hσ hqy hq2 i hi
  have hseq : 𝓝[S] (y, (0 : ℝ)) = 𝓝[{q : (X × ℂ) × ℝ | q.2 < 0}] (y, (0 : ℝ)) :=
    nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hrpos))
  have hsum := tendsto_iteratedFDeriv_discUnfoldSum hm (hW.prod isOpen_Ioo) hcd rfl hSgood hΦ
  have hev : (fun q => iteratedFDeriv ℝ m (discUnfoldExt k g) q) =ᶠ[𝓝[S] (y, (0 : ℝ))]
      (fun q => iteratedFDeriv ℝ m (discUnfoldSum (X := X) k g) q) := by
    refine Filter.eventually_of_mem self_mem_nhdsWithin fun q hq => ?_
    have hcut : ∀ i ∈ Finset.range (k + 1), |discScale i * q.2| < 1 := by
      intro i hi
      have hσ : |q.2| < θ := by
        have h1 : |q.2| ≤ dist q (y, (0 : ℝ)) := by
          rw [Prod.dist_eq, Real.dist_eq, sub_zero]
          exact le_max_right _ _
        exact lt_of_lt_of_le (lt_of_le_of_lt h1 hq.2) (min_le_right r₀ θ)
      exact abs_discScale_mul_lt_one hε hσ hi
    exact ((discUnfoldExt_eventuallyEq_discUnfoldSum hq.1 hcut).iteratedFDeriv ℝ m).eq_of_nhds
  have hres := hsum.congr' hev.symm
  rwa [hseq] at hres

/-- The limit of the iterated derivatives of the unfolded extension from the positive side agrees
with the limit of the iterated derivatives of `discUnfold g` from the positive side. -/
lemma tendsto_iteratedFDeriv_discUnfoldExt_pos {k m : ℕ} {g : X × ℂ → ℂ}
    {W : Set (X × ℂ)} (hW : IsOpen W) {ε : ℝ} (hε : 0 < ε)
    {y : X × ℂ} (hy : y ∈ W)
    {Φ : ContinuousMultilinearMap ℝ (fun _ : Fin m => (X × ℂ) × ℝ) ℂ}
    (hΦ : Tendsto (fun q => iteratedFDeriv ℝ m (discUnfold g) q)
        (𝓝[W ×ˢ Set.Ioo 0 ε] (y, (0 : ℝ))) (𝓝 Φ)) :
    Tendsto (fun q => iteratedFDeriv ℝ m (discUnfoldExt k g) q)
      (𝓝[{q : (X × ℂ) × ℝ | 0 < q.2}] (y, (0 : ℝ))) (𝓝 Φ) := by
  obtain ⟨r₀, hr₀pos, hr₀W⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hy)
  set r : ℝ := min r₀ ε with hrdef
  have hrpos : 0 < r := lt_min hr₀pos hε
  have hsub : {q : (X × ℂ) × ℝ | 0 < q.2} ∩ Metric.ball (y, (0 : ℝ)) r
      ⊆ W ×ˢ Set.Ioo 0 ε := by
    intro q hq
    refine ⟨?_, ?_⟩
    · refine hr₀W ?_
      have h1 : dist q.1 y ≤ dist q (y, (0 : ℝ)) := by
        rw [Prod.dist_eq]; exact le_max_left _ _
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt h1 (lt_of_lt_of_le hq.2 (min_le_left _ _))
    · refine ⟨hq.1, ?_⟩
      have h1 : |q.2| ≤ dist q (y, (0 : ℝ)) := by
        rw [Prod.dist_eq, Real.dist_eq, sub_zero]
        exact le_max_right _ _
      calc q.2 = |q.2| := (abs_of_pos hq.1).symm
        _ ≤ dist q (y, (0 : ℝ)) := h1
        _ < r := hq.2
        _ ≤ ε := min_le_right _ _
  have hball : Metric.ball (y, (0 : ℝ)) r ∈ 𝓝[{q : (X × ℂ) × ℝ | 0 < q.2}] (y, (0 : ℝ)) :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hrpos)
  have hU : Tendsto (fun q => iteratedFDeriv ℝ m (discUnfold g) q)
      (𝓝[{q : (X × ℂ) × ℝ | 0 < q.2}] (y, (0 : ℝ))) (𝓝 Φ) := by
    refine hΦ.mono_left ?_
    rw [← nhdsWithin_inter_of_mem' hball]
    exact nhdsWithin_mono _ hsub
  have hev : (fun q => iteratedFDeriv ℝ m (discUnfoldExt k g) q)
      =ᶠ[𝓝[{q : (X × ℂ) × ℝ | 0 < q.2}] (y, (0 : ℝ))]
      (fun q => iteratedFDeriv ℝ m (discUnfold g) q) := by
    refine Filter.eventually_of_mem self_mem_nhdsWithin fun q hq => ?_
    have hloc : discUnfoldExt k g =ᶠ[𝓝 q] discUnfold g :=
      Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_snd).mem_nhds hq)
        (fun r hr => discUnfoldExt_of_pos hr)
    exact (hloc.iteratedFDeriv ℝ m).eq_of_nhds
  exact hU.congr' hev.symm

/-- The limit of the unfolded extension along the hyperplane is its boundary value. -/
lemma tendsto_discUnfoldExt_trace {k : ℕ} {g : X × ℂ → ℂ} {W : Set (X × ℂ)} (hW : IsOpen W)
    (htrace : ContinuousOn (fun y : X × ℂ =>
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)).limUnder (fun σ : ℝ => discUnfold g (y, σ))) W)
    {y : X × ℂ} (hy : y ∈ W) :
    Tendsto (fun q : (X × ℂ) × ℝ => discUnfoldExt k g q)
      (𝓝[{q : (X × ℂ) × ℝ | q.2 = 0}] (y, (0 : ℝ)))
      (𝓝 (discUnfoldExt k g (y, 0))) := by
  have hpt : ∀ q : (X × ℂ) × ℝ, q.2 = 0 →
      discUnfoldExt k g q = (nhdsWithin (0 : ℝ) (Set.Ioi 0)).limUnder
        (fun σ : ℝ => discUnfold g (q.1, σ)) := fun q hq => discUnfoldExt_of_eq_zero hq
  have hFp : discUnfoldExt k g (y, (0 : ℝ)) =
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)).limUnder (fun σ : ℝ => discUnfold g (y, σ)) :=
    discUnfoldExt_of_eq_zero rfl
  have hmap : Tendsto (fun q : (X × ℂ) × ℝ => q.1)
      (𝓝[{q : (X × ℂ) × ℝ | q.2 = 0}] (y, (0 : ℝ))) (𝓝[W] y) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(continuous_fst.tendsto (y, (0 : ℝ))).mono_left nhdsWithin_le_nhds, ?_⟩
    exact nhdsWithin_le_nhds (continuous_fst.continuousAt.preimage_mem_nhds (hW.mem_nhds hy))
  have h1 : Tendsto (fun q : (X × ℂ) × ℝ =>
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)).limUnder (fun σ : ℝ => discUnfold g (q.1, σ)))
      (𝓝[{q : (X × ℂ) × ℝ | q.2 = 0}] (y, (0 : ℝ)))
      (𝓝 ((nhdsWithin (0 : ℝ) (Set.Ioi 0)).limUnder (fun σ : ℝ => discUnfold g (y, σ)))) := by
    have ht : Tendsto (fun y : X × ℂ =>
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)).limUnder (fun σ : ℝ => discUnfold g (y, σ)))
        (𝓝[W] y)
        (𝓝 ((nhdsWithin (0 : ℝ) (Set.Ioi 0)).limUnder (fun σ : ℝ => discUnfold g (y, σ)))) :=
      htrace.continuousWithinAt hy
    exact ht.comp hmap
  rw [hFp]
  refine h1.congr' ?_
  refine Filter.eventually_of_mem self_mem_nhdsWithin fun q hq => ?_
  exact (hpt q hq).symm

/-! ## The main theorem -/

theorem discUnfoldExt_contDiffOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {k : ℕ} {g : X × ℂ → ℂ} {β : ℝ} (hβ0 : 0 < β)
    {W : Set (X × ℂ)} (hW : IsOpen W) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ ≤ ε)
    (hcd : ContDiffOn ℝ (k : WithTop ENat) (Work.NN.DiscRadial.discUnfold g) (W ×ˢ Set.Ioo 0 ε))
    (hfin : Work.CR.Flat.holderNorm k β (Work.NN.DiscRadial.discUnfold g) (W ×ˢ Set.Ioo 0 ε) ≠ ⊤)
    (hN : ContDiffOn ℝ (k : WithTop ENat) (Work.NN.DiscRadial.discUnfoldExt k g)
      (W ×ˢ Set.Ioo (-δ) 0)) :
    ContDiffOn ℝ (k : WithTop ENat) (Work.NN.DiscRadial.discUnfoldExt k g)
      (W ×ˢ Set.Ioo (-δ) δ) := by
  have hΩopen : IsOpen (W ×ˢ Set.Ioo (0 : ℝ) ε) := hW.prod isOpen_Ioo
  have hVopen : IsOpen (W ×ˢ Set.Ioo (-δ) δ) := hW.prod isOpen_Ioo
  -- the boundary value of `discUnfold g` is continuous on `W`
  have htrace := continuousOn_traceLimUnder (G := (X × ℂ)) hβ0 hW hε hfin
  -- the hyperplane points lie in the closure of `Ω`
  have hclosure : ∀ y ∈ W, (y, (0 : ℝ)) ∈ closure (W ×ˢ Set.Ioo (0 : ℝ) ε) := by
    intro y hy
    rw [closure_prod_eq]
    exact ⟨subset_closure hy, by
      rw [closure_Ioo (ne_of_lt hε)]
      exact ⟨le_rfl, hε.le⟩⟩
  -- continuity of the extension on the slab
  have hc : ContinuousOn (discUnfoldExt k g) (W ×ˢ Set.Ioo (-δ) δ) := by
    rintro ⟨y, σ⟩ hp
    by_cases hσ : σ = 0
    · subst hσ
      have hy : y ∈ W := hp.1
      obtain ⟨Φ₀, hΦ₀⟩ := holderDerivTendsto_of_isOpen hβ0 hΩopen (discUnfold g) hfin
        (Nat.zero_le k) (hclosure y hy)
      let v : ℂ := (continuousMultilinearCurryFin0 ℝ ((X × ℂ) × ℝ) ℂ) Φ₀
      have hUlim : Tendsto (fun q => discUnfold g q) (𝓝[W ×ˢ Set.Ioo 0 ε] (y, (0 : ℝ))) (𝓝 v) :=
        tendsto_uncurry_zero hΦ₀
      haveI : NeBot (𝓝[>] (0 : ℝ)) := nhdsGT_neBot_of_exists_gt (a := (0 : ℝ)) ⟨1, by norm_num⟩
      have hvlim : Tendsto (fun σ : ℝ => discUnfold g (y, σ)) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
        have hmap : Tendsto (fun σ : ℝ => (y, σ)) (𝓝[>] (0 : ℝ))
            (𝓝[W ×ˢ Set.Ioo 0 ε] (y, (0 : ℝ))) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨((continuous_const.prodMk continuous_id).tendsto (0 : ℝ)).mono_left
            nhdsWithin_le_nhds, ?_⟩
          filter_upwards [Ioo_mem_nhdsGT hε] with σ hσ'
          exact ⟨hy, hσ'⟩
        exact hUlim.comp hmap
      have hFp : discUnfoldExt k g (y, (0 : ℝ)) = v := by
        rw [discUnfoldExt_of_eq_zero rfl]
        exact hvlim.limUnder_eq
      have hneg : Tendsto (fun q => discUnfoldExt k g q)
          (𝓝[{q : (X × ℂ) × ℝ | q.2 < 0}] (y, (0 : ℝ)))
          (𝓝 (discUnfoldExt k g (y, 0))) := by
        have h := tendsto_iteratedFDeriv_discUnfoldExt_neg (m := 0) (Nat.zero_le k) hW hε
          hcd hy hΦ₀
        have h2 := tendsto_uncurry_zero h
        rw [hFp]
        exact h2
      have hpos : Tendsto (fun q => discUnfoldExt k g q)
          (𝓝[{q : (X × ℂ) × ℝ | 0 < q.2}] (y, (0 : ℝ)))
          (𝓝 (discUnfoldExt k g (y, 0))) := by
        have h := tendsto_iteratedFDeriv_discUnfoldExt_pos (k := k) (m := 0) hW hε hy hΦ₀
        have h2 := tendsto_uncurry_zero h
        rw [hFp]
        exact h2
      have hzero : Tendsto (fun q => discUnfoldExt k g q)
          (𝓝[{q : (X × ℂ) × ℝ | q.2 = 0}] (y, (0 : ℝ)))
          (𝓝 (discUnfoldExt k g (y, 0))) :=
        tendsto_discUnfoldExt_trace (k := k) hW htrace hy
      have hset3 : ({q : (X × ℂ) × ℝ | q.2 < 0} ∪ {q : (X × ℂ) × ℝ | 0 < q.2}) ∪
          {q : (X × ℂ) × ℝ | q.2 = 0} = Set.univ := by
        ext q
        simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ]
        constructor
        · intro _; trivial
        · intro _
          rcases lt_trichotomy q.2 0 with h | h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
          · exact Or.inl (Or.inr h)
      have hsplit : 𝓝 (y, (0 : ℝ)) = 𝓝[{q : (X × ℂ) × ℝ | q.2 < 0}] (y, (0 : ℝ)) ⊔
          𝓝[{q : (X × ℂ) × ℝ | 0 < q.2}] (y, (0 : ℝ)) ⊔
          𝓝[{q : (X × ℂ) × ℝ | q.2 = 0}] (y, (0 : ℝ)) := by
        rw [← nhdsWithin_union, ← nhdsWithin_union, hset3, nhdsWithin_univ]
      have hcont : Tendsto (discUnfoldExt k g) (𝓝 (y, (0 : ℝ)))
          (𝓝 (discUnfoldExt k g (y, 0))) := by
        rw [hsplit]
        exact Filter.Tendsto.sup (Filter.Tendsto.sup hneg hpos) hzero
      exact (show ContinuousAt (discUnfoldExt k g) (y, (0 : ℝ)) from hcont).continuousWithinAt
    · rcases lt_or_gt_of_ne hσ with hlt | hgt
      · have hmem : (y, σ) ∈ W ×ˢ Set.Ioo (-δ) 0 := ⟨hp.1, ⟨hp.2.1, hlt⟩⟩
        exact ((hN.contDiffAt ((hW.prod isOpen_Ioo).mem_nhds hmem)).continuousAt).continuousWithinAt
      · have hmem : (y, σ) ∈ W ×ˢ Set.Ioo 0 ε := ⟨hp.1, ⟨hgt, lt_of_lt_of_le hp.2.2 hδε⟩⟩
        have hFcd : ContDiffAt ℝ (k : WithTop ENat) (discUnfoldExt k g) (y, σ) :=
          (hcd.contDiffAt (hΩopen.mem_nhds hmem)).congr_of_eventuallyEq
            (Filter.eventuallyEq_of_mem
              ((isOpen_lt continuous_const continuous_snd).mem_nhds hgt)
              (fun r hr => discUnfoldExt_of_pos hr))
        exact hFcd.continuousAt.continuousWithinAt
  -- the negative half space
  have hN' : ContDiffOn ℝ (k : WithTop ENat) (discUnfoldExt k g)
      ((W ×ˢ Set.Ioo (-δ) δ) ∩ {q : (X × ℂ) × ℝ | q.2 < 0}) := by
    have heq : (W ×ˢ Set.Ioo (-δ) δ) ∩ {q : (X × ℂ) × ℝ | q.2 < 0} = W ×ˢ Set.Ioo (-δ) 0 := by
      ext q
      constructor
      · intro hq
        exact ⟨hq.1.1, hq.1.2.1, hq.2⟩
      · intro hq
        exact ⟨⟨hq.1, hq.2.1, lt_of_lt_of_le hq.2.2 hδ.le⟩, hq.2.2⟩
    rw [heq]
    exact hN
  -- the positive half space
  have hH : ContDiffOn ℝ (k : WithTop ENat) (discUnfoldExt k g)
      ((W ×ˢ Set.Ioo (-δ) δ) ∩ {q : (X × ℂ) × ℝ | 0 < q.2}) := by
    have hsub : (W ×ˢ Set.Ioo (-δ) δ) ∩ {q : (X × ℂ) × ℝ | 0 < q.2}
        ⊆ W ×ˢ Set.Ioo 0 ε := by
      intro q hq
      exact ⟨hq.1.1, ⟨hq.2, lt_of_lt_of_le hq.1.2.2 hδε⟩⟩
    exact (hcd.mono hsub).congr fun q hq => discUnfoldExt_of_pos hq.2
  -- the limits along the punctured neighbourhoods of the hyperplane
  have hlim : ∀ i ≤ k, ∀ p ∈ W ×ˢ Set.Ioo (-δ) δ, p.2 = 0 →
      ∃ L : ContinuousMultilinearMap ℝ (fun _ : Fin i => (X × ℂ) × ℝ) ℂ,
      Tendsto (fun q => iteratedFDeriv ℝ i (discUnfoldExt k g) q)
        (𝓝[(W ×ˢ Set.Ioo (-δ) δ) ∩ {q : (X × ℂ) × ℝ | q.2 ≠ 0}] p) (𝓝 L) := by
    rintro i hi ⟨y, σ⟩ hp hσ
    subst hσ
    have hy : y ∈ W := hp.1
    obtain ⟨Φ, hΦ⟩ := holderDerivTendsto_of_isOpen hβ0 hΩopen (discUnfold g) hfin hi
      (hclosure y hy)
    refine ⟨Φ, ?_⟩
    have hneg := tendsto_iteratedFDeriv_discUnfoldExt_neg hi hW hε hcd hy hΦ
    have hpos := tendsto_iteratedFDeriv_discUnfoldExt_pos (k := k) (m := i) hW hε hy hΦ
    have h1 : Tendsto (fun q => iteratedFDeriv ℝ i (discUnfoldExt k g) q)
        (𝓝[(W ×ˢ Set.Ioo (-δ) δ) ∩ {q : (X × ℂ) × ℝ | q.2 < 0}] (y, (0 : ℝ))) (𝓝 Φ) :=
      hneg.mono_left (nhdsWithin_mono (y, (0 : ℝ)) fun q hq => hq.2)
    have h2 : Tendsto (fun q => iteratedFDeriv ℝ i (discUnfoldExt k g) q)
        (𝓝[(W ×ˢ Set.Ioo (-δ) δ) ∩ {q : (X × ℂ) × ℝ | 0 < q.2}] (y, (0 : ℝ))) (𝓝 Φ) :=
      hpos.mono_left (nhdsWithin_mono (y, (0 : ℝ)) fun q hq => hq.2)
    have h3 : Tendsto (fun q => iteratedFDeriv ℝ i (discUnfoldExt k g) q)
        (𝓝[((W ×ˢ Set.Ioo (-δ) δ) ∩ {q : (X × ℂ) × ℝ | q.2 < 0}) ∪
          ((W ×ˢ Set.Ioo (-δ) δ) ∩ {q : (X × ℂ) × ℝ | 0 < q.2})] (y, (0 : ℝ))) (𝓝 Φ) := by
      rw [nhdsWithin_union]
      exact Filter.Tendsto.sup h1 h2
    have hsetU : ((W ×ˢ Set.Ioo (-δ) δ) ∩ {q : (X × ℂ) × ℝ | q.2 < 0}) ∪
        ((W ×ˢ Set.Ioo (-δ) δ) ∩ {q : (X × ℂ) × ℝ | 0 < q.2})
        = (W ×ˢ Set.Ioo (-δ) δ) ∩ {q : (X × ℂ) × ℝ | q.2 ≠ 0} := by
      rw [← Set.inter_union_distrib_left]
      congr 1
      ext q
      rw [Set.mem_union, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
      constructor
      · rintro (h | h)
        · exact ne_of_lt h
        · exact ne_of_gt h
      · intro h
        rcases lt_or_gt_of_ne h with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
    rwa [hsetU] at h3
  exact glueOpen_local (X := X × ℂ) (Y := ℂ) hVopen hc hN' hH hlim

end Work.NN.DiscRadial
