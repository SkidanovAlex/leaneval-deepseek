import Mathlib
import Submission.Work.Diff.GE.EvolB.InteriorBound
import Submission.Work.Diff.GE.continuous_flow_quantities
import Submission.Work.Diff.GE.covRm_fixed_evol_cont
import Submission.Work.Diff.GE.hasDerivWithinAt_of_tendsto_deriv
import Submission.Work.Diff.GE.FlowCont.rmNormSq_continuousWithinAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The initial-time (`t = 0`) case of the fixed-vector `∇Rm` evolution estimate (`EvolB`)

The interior estimate `Work.Diff.GE.EvolB.covRm_fixed_evol_le_interior_B` covers `t ∈ (0,T)` of a
Ricci flow.  Because `IsRicciFlow G T` only gives joint smoothness of the metric family on the
*half-open* interval `[0,T)`, the point `t = 0` needs a separate argument.  It is done here with the
reparametrisation `τ ↦ τ²`:

* put `c τ := covRm (G (τ²)) x v a b c d` and `f s := covRm (G s) x v a b c d`; then
  `f = fun s ↦ c (√s)` on `[0,T)`, `c` is `C^∞` at `0` (it is the time slice of the jointly smooth
  family of `Work.Diff.GE.EvolB.covRmSliceSmooth` along the reparametrised flow
  `Work.Diff.GE.cfq_sqFlow`, which is jointly smooth on an *open* interval) and `c` is even;
* hence `c` has a second-order expansion at `0`, `Work.Diff.GE.deriv_eq_zero_of_even` gives
  `deriv c 0 = 0`, and `Work.Diff.GE.tendsto_deriv_comp_sqrt` shows that
  `deriv (fun s' ↦ c (√s'))` tends to `deriv (deriv c) 0 / 2` along `s ↓ 0`.  Since that function
  agrees with the interior derivative `covRmTimeDerivB reactionMap …` on `(0,T)`,
  `Work.Diff.GE.hasDerivWithinAt_of_tendsto_deriv` gives the one-sided derivative at `0`;
* the *bound* at `0` is the limit of the interior bounds, which needs the continuity at `0` of the
  right-hand side: `lapCovRmAt` (`Work.Diff.GE.EvolB.lapCovRmAt_continuousWithinAt`), `rmNormSq`
  (`Work.Diff.GE.FlowCont.rmNormSq_continuousWithinAt`), `dRmNormSq`
  (`Work.Diff.GE.cfq_dRmNormSq_continuousAt` + the reparametrisation transfer) and the four metric
  pairings (from the flow equation `∂ₜ g = -2 Ric`).

Everything in this file is stated with the two inputs `covRmSliceSmooth` and
`lapCovRmAt_continuousWithinAt` as *explicit hypotheses*, so that it can be compiled and used
independently of the two files that prove them; the instantiation is in `EvolB/Fix.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE.EvolB

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless] [T2Space M] [CompactSpace M]

/-- **The interior estimate in the form needed for the limit argument**: at an interior time the
*explicit* predicted derivative `covRmTimeDerivB reactionMap` (not merely *some* derivative) obeys
the bound.  This is `Work.Diff.GE.EvolB.covRm_fixed_evol_le_interior_B` combined with the
uniqueness of the one-sided derivative at an interior point, where
`Work.Diff.GE.EvolB.covRm_fixed_evol_interior_B` identifies the derivative. -/
theorem covRmTimeDerivB_le_interior_of (hLC : LCSmooth I M) (hLV : LCVariation I M) (C : ℝ)
    (hInt : ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, ∀ v a b c d : TangentSpace I x, ∃ D : ℝ,
        HasDerivWithinAt (fun s ↦ covRm (G s) x v a b c d) D (Set.Ico 0 T) t ∧
        D ≤ Work.Diff.GE.lapCovRmAt (G t) x v a b c d
            + C * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
              * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
                * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
                * Real.sqrt ((G t).inner x d d))) :
    ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, ∀ v a b c d : TangentSpace I x,
        covRmTimeDerivB reactionMap G t x v a b c d
          ≤ Work.Diff.GE.lapCovRmAt (G t) x v a b c d
            + C * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
              * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
                * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
                * Real.sqrt ((G t).inner x d d)) := by
  intro G T hflow t ht x v a b c d
  obtain ⟨D, hD, hDb⟩ := hInt G T hflow t ht x v a b c d
  have h2 := covRm_fixed_evol_interior_B (I := I) (M := M) hLC hLV hflow ht x v a b c d
  have hmem : Set.Ico (0 : ℝ) T ∈ 𝓝 t :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Ico_self
  have hD' : D = covRmTimeDerivB reactionMap G t x v a b c d :=
    (hD.hasDerivAt hmem).unique (h2.hasDerivAt hmem)
  rw [← hD']
  exact hDb

/-- **The interior estimate in the form needed for the limit argument** (with the constant
extracted): at an interior time the *explicit* predicted derivative `covRmTimeDerivB reactionMap`
obeys the bound. -/
theorem covRmTimeDerivB_le_interior_B
    (hLC : LCSmooth I M) (hLV : LCVariation I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, ∀ v a b c d : TangentSpace I x,
        covRmTimeDerivB reactionMap G t x v a b c d
          ≤ Work.Diff.GE.lapCovRmAt (G t) x v a b c d
            + C * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
              * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
                * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
                * Real.sqrt ((G t).inner x d d)) := by
  obtain ⟨C, hC, hInt⟩ := covRm_fixed_evol_le_interior_B (I := I) (M := M) hLC hLV
  exact ⟨C, hC, covRmTimeDerivB_le_interior_of (I := I) (M := M) hLC hLV C hInt⟩

/-- The four metric pairings along a Ricci flow are continuous at `0` within `[0,T)`. -/
theorem inner_continuousWithinAt_zero_B {G : ℝ → SMet I M} {T : ℝ} (hflow : IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ico 0 T) (x : M) (u v : TangentSpace I x) :
    ContinuousWithinAt (fun s : ℝ ↦ (G s).inner x u v) (Set.Ico 0 T) t :=
  (hflow.2 t ht x u v).continuousWithinAt

/-- Continuity of `|∇Rm|²` at `0` within `[0,T)`. -/
theorem dRmNormSq_continuousWithinAt_zero_B (hLC : LCSmooth I M)
    {G : ℝ → SMet I M} {T : ℝ} (hflow : IsRicciFlow G T) (x : M) :
    ContinuousWithinAt (fun s : ℝ ↦ dRmNormSq (G s) x) (Set.Ico 0 T) 0 := by
  by_cases hT : T ≤ 0
  · rw [Set.Ico_eq_empty_iff.mpr (not_lt.mpr hT)]
    simp [ContinuousWithinAt, nhdsWithin_empty]
  · have hTpos : 0 < T := not_le.mp hT
    set ρ : ℝ := Real.sqrt T / 2 with hρdef
    have hρ : 0 < ρ := by positivity
    have hρT : ρ ^ 2 < T := by
      rw [hρdef, div_pow, Real.sq_sqrt hTpos.le]
      nlinarith
    have hsq : JointSmooth (cfq_sqFlow G) (Set.Ioo (-ρ) ρ) :=
      cfq_jointSmooth_sqFlow (I := I) (M := M) G hTpos hρ hρT hflow.1
    have h0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
    have hcont : ContinuousAt (fun τ : ℝ ↦ dRmNormSq (cfq_sqFlow G τ) x) 0 :=
      cfq_dRmNormSq_continuousAt (I := I) (M := M) hLC isOpen_Ioo hsq h0 x
    refine cfq_continuousWithinAt_of_continuousAt_comp_sq hTpos hcont ?_
    intro s hs
    show dRmNormSq (G s) x = dRmNormSq (cfq_sqFlow G (Real.sqrt s)) x
    rw [show cfq_sqFlow G (Real.sqrt s) = G s from by
      rw [cfq_sqFlow, Real.sq_sqrt hs.1]]

/-- **The one-sided derivative of the fixed-vector `∇Rm` component at the initial time.**  With the
inputs `covRmSliceSmooth` (time smoothness of the slice along a jointly smooth family) and
`lapCovRmAt_continuousWithinAt` (continuity of the rough Laplacian at the initial time) as explicit
hypotheses, every component has a one-sided derivative at `0` along the flow, bounded by
`Δ∇Rm` at `0` plus `C |Rm| |∇Rm|` times the metric norms of the five arguments. -/
theorem covRm_fixed_evol_le_zero_of
    (hSlice : ∀ (G : ℝ → SMet I M) {J : Set ℝ}, IsOpen J → JointSmooth G J →
      ∀ t₀ ∈ J, ∀ x : M, ∀ v a b c d : TangentSpace I x,
        ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun t : ℝ ↦ covRm (G t) x v a b c d) t₀)
    (hBcont : ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T → ∀ x : M,
      ∀ v a b c d : TangentSpace I x,
        ContinuousWithinAt (fun s : ℝ ↦ Work.Diff.GE.lapCovRmAt (G s) x v a b c d)
          (Set.Ico 0 T) 0)
    (hLC : LCSmooth I M) (hLV : LCVariation I M)
    {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, ∀ v a b c d : TangentSpace I x,
        covRmTimeDerivB reactionMap G t x v a b c d
          ≤ Work.Diff.GE.lapCovRmAt (G t) x v a b c d
            + C * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
              * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
                * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
                * Real.sqrt ((G t).inner x d d))) :
    ∀ (G : ℝ → SMet I M) (T : ℝ), 0 < T → IsRicciFlow G T →
      ∀ x : M, ∀ v a b c d : TangentSpace I x, ∃ D : ℝ,
        HasDerivWithinAt (fun s : ℝ ↦ covRm (G s) x v a b c d) D (Set.Ico 0 T) 0 ∧
        D ≤ Work.Diff.GE.lapCovRmAt (G 0) x v a b c d
          + C * Real.sqrt (rmNormSq (G 0) x) * Real.sqrt (dRmNormSq (G 0) x)
            * (Real.sqrt ((G 0).inner x v v) * Real.sqrt ((G 0).inner x a a)
              * Real.sqrt ((G 0).inner x b b) * Real.sqrt ((G 0).inner x c c)
              * Real.sqrt ((G 0).inner x d d)) := by
  intro G T hTpos hflow x v a b c d
  -- the reparametrisation radius and the joint smoothness of the reparametrised flow
  set ρ : ℝ := Real.sqrt T / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρT : ρ ^ 2 < T := by
    rw [hρdef, div_pow, Real.sq_sqrt hTpos.le]
    nlinarith
  have hGJ : JointSmooth (cfq_sqFlow G) (Set.Ioo (-ρ) ρ) :=
    cfq_jointSmooth_sqFlow (I := I) (M := M) G hTpos hρ hρT hflow.1
  have h0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
  -- the reparametrised slice and the original slice
  set sl : ℝ → ℝ := fun τ ↦ covRm (cfq_sqFlow G τ) x v a b c d with hsldef
  set f : ℝ → ℝ := fun s ↦ covRm (G s) x v a b c d with hfdef
  set L : ℝ → ℝ := fun s ↦ covRmTimeDerivB reactionMap G s x v a b c d with hLdef
  -- `sl` is smooth at `0`, even, and differentiable near `0` from the right
  have hsl0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sl 0 := by
    have h := hSlice (cfq_sqFlow G) isOpen_Ioo hGJ 0 h0 x v a b c d
    simpa only [hsldef] using h
  have heven : ∀ τ : ℝ, sl (-τ) = sl τ := by
    intro τ
    simp only [hsldef, cfq_sqFlow, neg_sq]
  have hnear : ∀ᶠ u in 𝓝[>] (0 : ℝ), DifferentiableAt ℝ sl u := by
    have hpos : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Set.Ioo 0 ρ := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Iio_mem_nhds hρ] with u hu hupos
      exact ⟨hupos, hu⟩
    filter_upwards [hpos] with u hu
    have humem : u ∈ Set.Ioo (-ρ) ρ := ⟨by linarith [hu.1], hu.2⟩
    have h := hSlice (cfq_sqFlow G) isOpen_Ioo hGJ u humem x v a b c d
    exact h.differentiableAt (by simp)
  have hdsl : HasDerivAt (deriv sl) (deriv (deriv sl) 0) 0 :=
    (((hsl0.derivWithin (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by norm_num)).hasDerivAt)
  have hderiv0 : deriv sl 0 = 0 :=
    Work.Diff.GE.deriv_eq_zero_of_even heven (hsl0.differentiableAt (by simp))
  -- the limit of the derivative of `s ↦ sl (√s)` at `0⁺`
  have hlim : Filter.Tendsto (fun s : ℝ ↦ deriv (fun s' : ℝ ↦ sl (Real.sqrt s')) s)
      (𝓝[>] (0 : ℝ)) (𝓝 (deriv (deriv sl) 0 / 2)) :=
    Work.Diff.GE.tendsto_deriv_comp_sqrt hdsl hderiv0 hnear
  -- on `(0,T)` that derivative is the interior derivative `L`
  have hIoo : Set.Ioo (0 : ℝ) T ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hTpos
  have hIco : Set.Ico (0 : ℝ) T ∈ 𝓝[>] (0 : ℝ) :=
    Filter.mem_of_superset hIoo (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have hle : (𝓝[>] (0 : ℝ)) ≤ 𝓝[Set.Ico 0 T] 0 := nhdsWithin_le_iff.mpr hIco
  have heq : (fun s : ℝ ↦ deriv (fun s' : ℝ ↦ sl (Real.sqrt s')) s) =ᶠ[𝓝[>] (0 : ℝ)] L := by
    filter_upwards [hIoo] with s hs
    have hagree : (fun s' : ℝ ↦ sl (Real.sqrt s')) =ᶠ[𝓝 s] f := by
      have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝 s := IsOpen.mem_nhds isOpen_Ioi hs.1
      filter_upwards [hmem] with s' hs'
      simp only [hsldef, hfdef, cfq_sqFlow, Real.sq_sqrt (le_of_lt hs')]
    rw [hagree.deriv_eq]
    have hmem : Set.Ico (0 : ℝ) T ∈ 𝓝 s :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs) Set.Ioo_subset_Ico_self
    exact ((covRm_fixed_evol_interior_B (I := I) (M := M) hLC hLV hflow hs x v a b c d
      ).hasDerivAt hmem).deriv
  have hLlim : Filter.Tendsto L (𝓝[>] (0 : ℝ)) (𝓝 (deriv (deriv sl) 0 / 2)) :=
    hlim.congr' heq
  -- the derivative of `f` on the interior and its continuity at `0`
  have hderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt f (L t) t := by
    intro t ht
    have hmem : Set.Ico (0 : ℝ) T ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Ico_self
    have h := (covRm_fixed_evol_interior_B (I := I) (M := M) hLC hLV hflow ht x v a b c d
      ).hasDerivAt hmem
    simpa only [hLdef, hfdef] using h
  have hcontf : ContinuousWithinAt f (Set.Ico 0 T) 0 :=
    cfq_continuousWithinAt_of_continuousAt_comp_sq (f := f) hTpos
      hsl0.continuousAt
      (fun s hs => by simp only [hsldef, hfdef, cfq_sqFlow, Real.sq_sqrt hs.1])
  -- the one-sided derivative at `0` from the boundary differentiability theorem
  have hdf : DifferentiableOn ℝ f (Set.Ioo 0 T) :=
    fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt
  have hcw : ContinuousWithinAt f (Set.Ioo 0 T) 0 :=
    hcontf.mono (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have heqf : deriv f =ᶠ[𝓝[>] (0 : ℝ)] L := by
    filter_upwards [hIoo] with s hs
    exact (hderiv s hs).deriv
  have hlimf : Filter.Tendsto (deriv f) (𝓝[>] (0 : ℝ)) (𝓝 (deriv (deriv sl) 0 / 2)) :=
    hLlim.congr' heqf.symm
  have hbdd : HasDerivWithinAt f (deriv (deriv sl) 0 / 2) (Set.Ici 0) 0 :=
    hasDerivWithinAt_Ici_of_tendsto_deriv hdf hcw hIoo hlimf
  refine ⟨deriv (deriv sl) 0 / 2, hbdd.mono Set.Ico_subset_Ici_self, ?_⟩
  -- the bound: the limit of the interior bounds
  have hBc : ContinuousWithinAt (fun s : ℝ ↦ Work.Diff.GE.lapCovRmAt (G s) x v a b c d)
      (Set.Ico 0 T) 0 := hBcont G T hflow x v a b c d
  have hBlim : Filter.Tendsto (fun s : ℝ ↦ Work.Diff.GE.lapCovRmAt (G s) x v a b c d)
      (𝓝[>] (0 : ℝ)) (𝓝 (Work.Diff.GE.lapCovRmAt (G 0) x v a b c d)) :=
    hBc.tendsto.mono_left hle
  have hrm : ContinuousWithinAt (fun s : ℝ ↦ rmNormSq (G s) x) (Set.Ico 0 T) 0 :=
    Work.Diff.GE.FlowCont.rmNormSq_continuousWithinAt (I := I) (M := M) hLC hflow
      ⟨le_refl (0 : ℝ), hTpos⟩ x
  have hdrm : ContinuousWithinAt (fun s : ℝ ↦ dRmNormSq (G s) x) (Set.Ico 0 T) 0 :=
    dRmNormSq_continuousWithinAt_zero_B (I := I) (M := M) hLC hflow x
  have hvv : ContinuousWithinAt (fun s : ℝ ↦ (G s).inner x v v) (Set.Ico 0 T) 0 :=
    inner_continuousWithinAt_zero_B hflow ⟨le_refl (0 : ℝ), hTpos⟩ x v v
  have haa : ContinuousWithinAt (fun s : ℝ ↦ (G s).inner x a a) (Set.Ico 0 T) 0 :=
    inner_continuousWithinAt_zero_B hflow ⟨le_refl (0 : ℝ), hTpos⟩ x a a
  have hbb : ContinuousWithinAt (fun s : ℝ ↦ (G s).inner x b b) (Set.Ico 0 T) 0 :=
    inner_continuousWithinAt_zero_B hflow ⟨le_refl (0 : ℝ), hTpos⟩ x b b
  have hcc : ContinuousWithinAt (fun s : ℝ ↦ (G s).inner x c c) (Set.Ico 0 T) 0 :=
    inner_continuousWithinAt_zero_B hflow ⟨le_refl (0 : ℝ), hTpos⟩ x c c
  have hdd : ContinuousWithinAt (fun s : ℝ ↦ (G s).inner x d d) (Set.Ico 0 T) 0 :=
    inner_continuousWithinAt_zero_B hflow ⟨le_refl (0 : ℝ), hTpos⟩ x d d
  have hRHS : Filter.Tendsto (fun s : ℝ ↦ Work.Diff.GE.lapCovRmAt (G s) x v a b c d
      + C * (Real.sqrt (rmNormSq (G s) x) * Real.sqrt (dRmNormSq (G s) x)
        * (Real.sqrt ((G s).inner x v v) * Real.sqrt ((G s).inner x a a)
          * Real.sqrt ((G s).inner x b b) * Real.sqrt ((G s).inner x c c)
          * Real.sqrt ((G s).inner x d d)))) (𝓝[>] (0 : ℝ))
      (𝓝 (Work.Diff.GE.lapCovRmAt (G 0) x v a b c d
        + C * (Real.sqrt (rmNormSq (G 0) x) * Real.sqrt (dRmNormSq (G 0) x)
          * (Real.sqrt ((G 0).inner x v v) * Real.sqrt ((G 0).inner x a a)
            * Real.sqrt ((G 0).inner x b b) * Real.sqrt ((G 0).inner x c c)
            * Real.sqrt ((G 0).inner x d d))))) := by
    refine hBlim.add ?_
    have hprod : Filter.Tendsto (fun s : ℝ ↦ Real.sqrt (rmNormSq (G s) x)
        * Real.sqrt (dRmNormSq (G s) x)
          * (Real.sqrt ((G s).inner x v v) * Real.sqrt ((G s).inner x a a)
            * Real.sqrt ((G s).inner x b b) * Real.sqrt ((G s).inner x c c)
            * Real.sqrt ((G s).inner x d d))) (𝓝[>] (0 : ℝ))
        (𝓝 (Real.sqrt (rmNormSq (G 0) x) * Real.sqrt (dRmNormSq (G 0) x)
          * (Real.sqrt ((G 0).inner x v v) * Real.sqrt ((G 0).inner x a a)
            * Real.sqrt ((G 0).inner x b b) * Real.sqrt ((G 0).inner x c c)
            * Real.sqrt ((G 0).inner x d d)))) := by
      have h1 : Filter.Tendsto (fun s : ℝ ↦ Real.sqrt (rmNormSq (G s) x)
          * Real.sqrt (dRmNormSq (G s) x)) (𝓝[>] (0 : ℝ))
          (𝓝 (Real.sqrt (rmNormSq (G 0) x) * Real.sqrt (dRmNormSq (G 0) x))) :=
        (hrm.tendsto.mono_left hle).sqrt.mul (hdrm.tendsto.mono_left hle).sqrt
      have h2 : Filter.Tendsto (fun s : ℝ ↦ Real.sqrt ((G s).inner x v v)
          * Real.sqrt ((G s).inner x a a) * Real.sqrt ((G s).inner x b b)
          * Real.sqrt ((G s).inner x c c) * Real.sqrt ((G s).inner x d d)) (𝓝[>] (0 : ℝ))
          (𝓝 (Real.sqrt ((G 0).inner x v v) * Real.sqrt ((G 0).inner x a a)
            * Real.sqrt ((G 0).inner x b b) * Real.sqrt ((G 0).inner x c c)
            * Real.sqrt ((G 0).inner x d d))) :=
        ((((hvv.tendsto.mono_left hle).sqrt.mul (haa.tendsto.mono_left hle).sqrt).mul
          (hbb.tendsto.mono_left hle).sqrt).mul (hcc.tendsto.mono_left hle).sqrt).mul
          (hdd.tendsto.mono_left hle).sqrt
      exact h1.mul h2
    exact hprod.const_mul C
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), L s ≤ Work.Diff.GE.lapCovRmAt (G s) x v a b c d
      + C * (Real.sqrt (rmNormSq (G s) x) * Real.sqrt (dRmNormSq (G s) x)
        * (Real.sqrt ((G s).inner x v v) * Real.sqrt ((G s).inner x a a)
          * Real.sqrt ((G s).inner x b b) * Real.sqrt ((G s).inner x c c)
          * Real.sqrt ((G s).inner x d d))) := by
    filter_upwards [hIoo] with s hs
    have h := hBound G T hflow s hs x v a b c d
    simp only [hLdef] at h ⊢
    linarith [h]
  haveI : NeBot (𝓝[>] (0 : ℝ)) := nhdsGT_neBot_of_exists_gt ⟨T, hTpos⟩
  have hbound := le_of_tendsto_of_tendsto hLlim hRHS hev
  linarith [hbound]

end Work.Diff.GE.EvolB
