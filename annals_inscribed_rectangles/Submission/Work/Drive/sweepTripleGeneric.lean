import Mathlib
import Submission.Work.Drive.sweepPertSurjDef
import Submission.Work.Drive.sweepPertSurj_of_chartPert
import Submission.Work.Drive.chartShiftHsurj
import Submission.Work.Drive.exists_meet3Hyp_of_good_family
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.contMDiff_clampedSweep_family
import Submission.Work.Drive.sideGermDefs

/-!
# The genericity of the design's triple of chart-perturbed clamped sweeps

This file supplies the *genericity* input of the triple-counting route for the design's family of
three clamped sweeps whose plane presentations are perturbed by a `Work.Drive.ChartPert`:

> `G t k x = clampedSweep (c k) (fun s => 1 - s) (fun z => Ξ (blk k t) (diskPlane Q z)) x`,
> `t : 𝔼^12 = (𝔼^4)³` (one `𝔼^4`-block of perturbation per chain).

The outputs are

* **§1** — the *strengthened* sweep-perturbation brick: the parameter-derivative of
  `t' ↦ clampedSweep c (1 - ·) (Ξ t' ∘ diskPlane Q) y` is onto as soon as the radial parameter `y 2`
  is nonzero (no box and no `y 2 ∈ (0,1)` hypothesis).  This is the form the triple genericity needs:
  at a triple meet at most one chain can sit on its *floor* (`y 2 = 0`), because the three truncation
  levels `c k` are distinct, and the other two chains then supply the surjectivity.
* **§2** — the relaxed criterion `Work.Drive.TParity.surjective_fderiv_chartDiff3_of_pair*`: only
  *two* of the three chains are required to admit directions that move them while freezing the third.
  (The existing `..._of_block` requires this for all three.)
* **§3** — the design's family, its joint smoothness (from the independent brick
  `Work.Drive.contMDiff_clampedSweep_family` of `contMDiff_clampedSweep_family.lean`), the `hsurj`
  derivation above, and the assembly into
  `Work.Drive.exists_meet3Hyp_sweepChartFam` (via `Work.Drive.exists_meet3Hyp_of_good_family`).
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

-- The `ChartPert` predicate is stated for a chart `Q`, but its content does not involve `Q` (the
-- chart is only the *name* of the perturbation's base); this binding makes the parameter explicit.
variable {Q : ℂ → CappingSpace}

/-! ## 1. The strengthened sweep-perturbation surjectivity -/

/-- **The `hsurj` brick for chart-perturbed clamped sweeps, in the sharp form**: if the radial
parameter `y 2` of the sweep is nonzero (no box membership and no upper bound are needed), then the
parameter-derivative of `t' ↦ clampedSweep c (1 - ·) (Ξ t' ∘ diskPlane Q) y` is onto.

This is `Work.Drive.sweepPertSurj_of_chartPert` with the hypothesis `y 2 ∈ (0,1)` weakened to
`y 2 ≠ 0`; the proof is the same (the only use of the hypothesis is `y 2 ≠ 0`, in the exponent
condition of the reciprocal dilation `dil`). -/
theorem surjective_mfderiv_clampedSweep_ne_zero {Q : ℂ → CappingSpace} {m : ℕ}
    {Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace} (hΞ : ChartPert Q m Ξ)
    {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (c : ℝ) (hc : 0 < c) (y : EuclideanSpace ℝ (Fin 3)) (hyne : y 2 ≠ 0)
    (t : EuclideanSpace ℝ (Fin m)) :
    Function.Surjective
      (mfderiv (𝓡 m) (𝓡 4)
        (fun t' => clampedSweep c (fun s => 1 - s) (fun z => Ξ t' (P z)) y) t) := by
  have hab : (1 - y 2) + (-(1 - y 2) / (y 2)) - (1 - y 2) * (-(1 - y 2) / (y 2)) = 0 := by
    field_simp
    ring
  set u : EuclideanSpace ℝ (Fin m) → CappingSpace :=
    fun t' => Ξ t' (P (mk2 (y 0) (y 1)))
  have hmd_u : MDifferentiableAt (𝓡 m) (𝓡 4) u t := by
    have hpair : ContMDiffAt (𝓡 m) ((𝓡 m).prod (𝓡 4)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t' : EuclideanSpace ℝ (Fin m) =>
          (t', P (mk2 (y 0) (y 1)))) t :=
      ContMDiffAt.prodMk contMDiffAt_id contMDiffAt_const
    exact ((hΞ.2.1.contMDiffAt (x := (t, P (mk2 (y 0) (y 1))))).comp t hpair).mdifferentiableAt
      (by simp)
  have hsurj_u : Function.Surjective (mfderiv (𝓡 m) (𝓡 4) u t) := hΞ.2.2 t _
  have hmd_G : MDifferentiableAt (𝓡 4) (𝓡 4) (dil c (1 - y 2)) (u t) :=
    (contMDiffAt_dil c (1 - y 2) (u t)).mdifferentiableAt (by simp)
  have hsurj_G : Function.Surjective (mfderiv (𝓡 4) (𝓡 4) (dil c (1 - y 2)) (u t)) :=
    surjective_mfderiv_dil c hc hab (u t)
  have hfun : (fun t' => clampedSweep c (fun s => 1 - s) (fun z => Ξ t' (P z)) y)
      = (dil c (1 - y 2)) ∘ u := by
    funext t'
    rfl
  rw [hfun]
  have hchain := mfderiv_comp (I := 𝓡 m) (I' := 𝓡 4) (I'' := 𝓡 4)
    (f := u) (g := dil c (1 - y 2)) t hmd_G hmd_u
  rw [hchain]
  exact hsurj_G.comp hsurj_u

/-- The charted form of `Work.Drive.surjective_mfderiv_clampedSweep_ne_zero`: the derivative of the
*charted* family is onto, which is the shape the parametric-Sard engines consume. -/
theorem surjective_fderiv_chart_clampedSweep_ne_zero {Q : ℂ → CappingSpace} {m : ℕ}
    {Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace} (hΞ : ChartPert Q m Ξ)
    {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (c : ℝ) (hc : 0 < c) (y : EuclideanSpace ℝ (Fin 3)) (hyne : y 2 ≠ 0)
    (t : EuclideanSpace ℝ (Fin m)) (p : CappingSpace)
    (hsrc : clampedSweep c (fun s => 1 - s) (fun z => Ξ t (P z)) y ∈ (chr p).source)
    (hsm : ContMDiff (𝓡 m) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t' => clampedSweep c (fun s => 1 - s) (fun z => Ξ t' (P z)) y)) :
    Function.Surjective
      (fderiv ℝ (fun t' => chr p
        (clampedSweep c (fun s => 1 - s) (fun z => Ξ t' (P z)) y)) t) :=
  surjective_fderiv_chart_comp p hsm hsrc
    (surjective_mfderiv_clampedSweep_ne_zero hΞ c hc y hyne t)

/-! ## 2. The relaxed block criteria for the charted triple difference -/

/-- **The charted pair map is onto as soon as the two charted differences can be prescribed.**

Given the charted derivatives `D k` of a triple of chains, if for every `(w₁,w₂)` there is a parameter
`u` with `D 0 u - D 1 u = w₁` and `D 0 u - D 2 u = w₂`, then the parameter-derivative of the charted
difference map `Work.Drive.TParity.chartDiff3` is onto.  This is the common core of the three relaxed
block criteria below (the existing `Work.Drive.TParity.surjective_fderiv_chartDiff3_of_block` is the
special case in which the prescribed values are built from the two *blocks* `1` and `2`). -/
theorem TParity.surjective_fderiv_chartDiff3_of_prescribed (m : ℕ)
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (p : M) (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9))
    (D : Fin 3 → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (hD : ∀ k : Fin 3, HasFDerivAt
      (fun t' => (Work.Drive.chr p) (G t' k (Work.Drive.TParity.bPartC k y))) (D k) t)
    (hsplit : ∀ w₁ w₂ : EuclideanSpace ℝ (Fin 4), ∃ u : EuclideanSpace ℝ (Fin m),
      D 0 u - D 1 u = w₁ ∧ D 0 u - D 2 u = w₂) :
    Function.Surjective
      (fderiv ℝ (fun t' => Work.Drive.TParity.chartDiff3 p (G t') y) t) := by
  have hpair : HasFDerivAt
      (fun t' : EuclideanSpace ℝ (Fin m) =>
        (((Work.Drive.chr p) (G t' 0 (Work.Drive.TParity.bPartC 0 y)) -
            (Work.Drive.chr p) (G t' 1 (Work.Drive.TParity.bPartC 1 y))),
          ((Work.Drive.chr p) (G t' 0 (Work.Drive.TParity.bPartC 0 y)) -
            (Work.Drive.chr p) (G t' 2 (Work.Drive.TParity.bPartC 2 y)))))
      ((D 0 - D 1).prod (D 0 - D 2)) t :=
    ((hD 0).sub (hD 1)).prodMk ((hD 0).sub (hD 2))
  have hcomp : HasFDerivAt
      (fun t' : EuclideanSpace ℝ (Fin m) =>
        Work.Drive.TParity.pUp ((Work.Drive.chr p) (G t' 0 (Work.Drive.TParity.bPartC 0 y)) -
            (Work.Drive.chr p) (G t' 1 (Work.Drive.TParity.bPartC 1 y)))
          ((Work.Drive.chr p) (G t' 0 (Work.Drive.TParity.bPartC 0 y)) -
            (Work.Drive.chr p) (G t' 2 (Work.Drive.TParity.bPartC 2 y))))
      (Work.Drive.TParity.pUpCLM.comp ((D 0 - D 1).prod (D 0 - D 2))) t := by
    have h1 := Work.Drive.TParity.pUpCLM.hasFDerivAt.comp t hpair
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t' => ?_))
    exact (Work.Drive.TParity.pUpCLM_apply
      ((Work.Drive.chr p) (G t' 0 (Work.Drive.TParity.bPartC 0 y)) -
        (Work.Drive.chr p) (G t' 1 (Work.Drive.TParity.bPartC 1 y)))
      ((Work.Drive.chr p) (G t' 0 (Work.Drive.TParity.bPartC 0 y)) -
        (Work.Drive.chr p) (G t' 2 (Work.Drive.TParity.bPartC 2 y)))).symm
  have hfinal : HasFDerivAt
      (fun t' => Work.Drive.TParity.chartDiff3 p (G t') y)
      (Work.Drive.TParity.pUpCLM.comp ((D 0 - D 1).prod (D 0 - D 2))) t :=
    hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t' => by
      simp only [Work.Drive.TParity.chartDiff3, Work.Drive.TParity.pUp]))
  rw [hfinal.fderiv]
  intro w
  set w₁ : EuclideanSpace ℝ (Fin 4) :=
    WithLp.toLp 2 (fun j : Fin 4 => w.ofLp (Fin.castAdd 4 j)) with hw₁
  set w₂ : EuclideanSpace ℝ (Fin 4) :=
    WithLp.toLp 2 (fun j : Fin 4 => w.ofLp (Fin.natAdd 4 j)) with hw₂
  obtain ⟨u, hu₁, hu₂⟩ := hsplit w₁ w₂
  have hstack : Work.Drive.pairUp w₁ w₂ = w := by
    apply WithLp.ofLp_injective 2
    funext i
    rw [show (Work.Drive.pairUp w₁ w₂).ofLp i = (if h : i.val < 4 then
        w₁ ⟨i.val, h⟩ else w₂ ⟨i.val - 4, by omega⟩) from rfl]
    by_cases h : i.val < 4
    · rw [dif_pos h, hw₁]
      refine congrArg w.ofLp ?_
      exact Fin.ext rfl
    · rw [dif_neg h, hw₂]
      refine congrArg w.ofLp ?_
      refine Fin.ext ?_
      simp only [Fin.natAdd]
      omega
  refine ⟨u, ?_⟩
  have hp : ((D 0 - D 1).prod (D 0 - D 2)) u = (w₁, w₂) := by
    rw [ContinuousLinearMap.prod_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.sub_apply]
    exact Prod.ext hu₁ hu₂
  have hkey : Work.Drive.TParity.pUpCLM
      (((D 0 - D 1).prod (D 0 - D 2)) u) = w := by
    rw [hp, Work.Drive.TParity.pUpCLM_apply w₁ w₂]
    exact hstack
  exact hkey

/-- **The relaxed block criterion, free blocks `1` and `2`.**  Only the two chains `1` and `2` need
directions that move them while freezing the third (chain `0`); chain `0` is then used freely. -/
theorem TParity.surjective_fderiv_chartDiff3_of_pair12 (m : ℕ)
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (p : M) (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9))
    (D : Fin 3 → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (hD : ∀ k : Fin 3, HasFDerivAt
      (fun t' => (Work.Drive.chr p) (G t' k (Work.Drive.TParity.bPartC k y))) (D k) t)
    (h1 : ∀ z : EuclideanSpace ℝ (Fin 4), ∃ u : EuclideanSpace ℝ (Fin m),
      D 1 u = z ∧ D 0 u = 0 ∧ D 2 u = 0)
    (h2 : ∀ z : EuclideanSpace ℝ (Fin 4), ∃ u : EuclideanSpace ℝ (Fin m),
      D 2 u = z ∧ D 0 u = 0 ∧ D 1 u = 0) :
    Function.Surjective
      (fderiv ℝ (fun t' => Work.Drive.TParity.chartDiff3 p (G t') y) t) := by
  refine TParity.surjective_fderiv_chartDiff3_of_prescribed m G p t y D hD ?_
  intro w₁ w₂
  obtain ⟨u₁, hu₁, hu₁₀, hu₁₂⟩ := h1 (-w₁)
  obtain ⟨u₂, hu₂, hu₂₀, hu₂₁⟩ := h2 (-w₂)
  refine ⟨u₁ + u₂, ?_, ?_⟩
  · simp only [map_add, hu₁₀, hu₂₀, hu₁, hu₂₁]
    abel
  · simp only [map_add, hu₁₀, hu₂₀, hu₁₂, hu₂]
    abel

/-- **The relaxed block criterion, free blocks `0` and `2`.** -/
theorem TParity.surjective_fderiv_chartDiff3_of_pair02 (m : ℕ)
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (p : M) (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9))
    (D : Fin 3 → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (hD : ∀ k : Fin 3, HasFDerivAt
      (fun t' => (Work.Drive.chr p) (G t' k (Work.Drive.TParity.bPartC k y))) (D k) t)
    (h0 : ∀ z : EuclideanSpace ℝ (Fin 4), ∃ u : EuclideanSpace ℝ (Fin m),
      D 0 u = z ∧ D 1 u = 0 ∧ D 2 u = 0)
    (h2 : ∀ z : EuclideanSpace ℝ (Fin 4), ∃ u : EuclideanSpace ℝ (Fin m),
      D 2 u = z ∧ D 0 u = 0 ∧ D 1 u = 0) :
    Function.Surjective
      (fderiv ℝ (fun t' => Work.Drive.TParity.chartDiff3 p (G t') y) t) := by
  refine TParity.surjective_fderiv_chartDiff3_of_prescribed m G p t y D hD ?_
  intro w₁ w₂
  obtain ⟨u₀, hu₀, hu₀₁, hu₀₂⟩ := h0 w₁
  obtain ⟨u₂, hu₂, hu₂₀, hu₂₁⟩ := h2 (w₁ - w₂)
  refine ⟨u₀ + u₂, ?_, ?_⟩
  · simp only [map_add, hu₀, hu₂₀, hu₀₁, hu₂₁]
    abel
  · simp only [map_add, hu₀, hu₂₀, hu₀₂, hu₂]
    abel

/-- **The relaxed block criterion, free blocks `0` and `1`.** -/
theorem TParity.surjective_fderiv_chartDiff3_of_pair01 (m : ℕ)
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (p : M) (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9))
    (D : Fin 3 → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (hD : ∀ k : Fin 3, HasFDerivAt
      (fun t' => (Work.Drive.chr p) (G t' k (Work.Drive.TParity.bPartC k y))) (D k) t)
    (h0 : ∀ z : EuclideanSpace ℝ (Fin 4), ∃ u : EuclideanSpace ℝ (Fin m),
      D 0 u = z ∧ D 1 u = 0 ∧ D 2 u = 0)
    (h1 : ∀ z : EuclideanSpace ℝ (Fin 4), ∃ u : EuclideanSpace ℝ (Fin m),
      D 1 u = z ∧ D 0 u = 0 ∧ D 2 u = 0) :
    Function.Surjective
      (fderiv ℝ (fun t' => Work.Drive.TParity.chartDiff3 p (G t') y) t) := by
  refine TParity.surjective_fderiv_chartDiff3_of_prescribed m G p t y D hD ?_
  intro w₁ w₂
  obtain ⟨u₀, hu₀, hu₀₁, hu₀₂⟩ := h0 w₂
  obtain ⟨u₁, hu₁, hu₁₀, hu₁₂⟩ := h1 (w₂ - w₁)
  refine ⟨u₀ + u₁, ?_, ?_⟩
  · simp only [map_add, hu₀, hu₀₁, hu₁, hu₁₀]
    abel
  · simp only [map_add, hu₀, hu₀₂, hu₁₀, hu₁₂]
    abel

/-- **The pair directions come from a block decomposition.**  If each charted derivative is the
composite of a block derivative `B k` with the block projection `π k` of the parameter, and the blocks
`i` and `l` are free (their projections are separately surjective), then the two chains `i` and `l`
admit directions that move them while freezing the third. -/
theorem pairFree_of_blockSurjective {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (π : Fin 3 → EuclideanSpace ℝ (Fin m) →L[ℝ] F) (B : Fin 3 → F →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (D : Fin 3 → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (hdec : ∀ k : Fin 3, D k = (B k).comp (π k))
    (hjoin : ∀ v : Fin 3 → F, ∃ u : EuclideanSpace ℝ (Fin m), ∀ k : Fin 3, π k u = v k)
    {i j l : Fin 3} (hij : i ≠ j) (hil : i ≠ l)
    (hi : Function.Surjective (B i)) :
    ∀ z : EuclideanSpace ℝ (Fin 4), ∃ u : EuclideanSpace ℝ (Fin m),
      D i u = z ∧ D j u = 0 ∧ D l u = 0 := by
  intro z
  obtain ⟨w, hw⟩ := hi z
  refine ⟨Classical.choose (hjoin (fun k => if k = i then w else 0)), ?_, ?_, ?_⟩
  · rw [hdec i, ContinuousLinearMap.comp_apply,
      Classical.choose_spec (hjoin (fun k => if k = i then w else 0)) i, if_pos rfl, hw]
  · rw [hdec j, ContinuousLinearMap.comp_apply,
      Classical.choose_spec (hjoin (fun k => if k = i then w else 0)) j, if_neg (Ne.symm hij),
      map_zero]
  · rw [hdec l, ContinuousLinearMap.comp_apply,
      Classical.choose_spec (hjoin (fun k => if k = i then w else 0)) l, if_neg (Ne.symm hil),
      map_zero]

/-! ## 3. The design's family of chart-perturbed clamped sweeps -/

/-- **The slice of the design's family in one perturbation block**: the `k`-th chain, presented by the
plane `P k`, as a function of the block parameter `s ∈ 𝔼^4` and of the sweep parameter `x ∈ 𝔼^3`. -/
def sweepChartSlice (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (c : Fin 3 → ℝ) (k : Fin 3) (s : EuclideanSpace ℝ (Fin 4))
    (x : EuclideanSpace ℝ (Fin 3)) : CappingSpace :=
  clampedSweep (c k) (fun r => 1 - r) (fun z => Ξ s (P k z)) x

/-- **The design's family**: the `k`-th chain is the clamped sweep of the `k`-th plane presentation
`P k`, with its chart perturbed by the `k`-th block of the parameter `t ∈ 𝔼^12` and with the truncation
level `c k`.  The plane presentations `P k` are *data* (they may be the rotations
`rotPresentation Q (u k)` of one chart, which is the design's triple). -/
def sweepChartFam (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (c : Fin 3 → ℝ) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3)
    (x : EuclideanSpace ℝ (Fin 3)) : CappingSpace :=
  clampedSweep (c k) (fun r => 1 - r) (fun z => Ξ (blk k t) (P k z)) x

@[simp] lemma sweepChartSlice_apply (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (c : Fin 3 → ℝ) (k : Fin 3) (s : EuclideanSpace ℝ (Fin 4))
    (x : EuclideanSpace ℝ (Fin 3)) :
    sweepChartSlice P Ξ c k s x
      = clampedSweep (c k) (fun r => 1 - r) (fun z => Ξ s (P k z)) x := rfl

@[simp] lemma sweepChartFam_apply (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (c : Fin 3 → ℝ) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3)
    (x : EuclideanSpace ℝ (Fin 3)) :
    sweepChartFam P Ξ c t k x
      = clampedSweep (c k) (fun r => 1 - r) (fun z => Ξ (blk k t) (P k z)) x := rfl

/-- The `k`-th chain of the family is the slice at the `k`-th block of the parameter. -/
lemma sweepChartFam_eq_slice (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (c : Fin 3 → ℝ) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3)
    (x : EuclideanSpace ℝ (Fin 3)) :
    sweepChartFam P Ξ c t k x = sweepChartSlice P Ξ c k (blk k t) x := rfl

/-- The family at a parameter concentrated in the `k`-th block is the slice. -/
lemma sweepChartFam_blkSpan (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (c : Fin 3 → ℝ) (k : Fin 3) (s : EuclideanSpace ℝ (Fin 4))
    (x : EuclideanSpace ℝ (Fin 3)) :
    sweepChartFam P Ξ c (blkSpan k s) k x = sweepChartSlice P Ξ c k s x := by
  simp only [sweepChartFam, sweepChartSlice, blk_blkSpan]

/-- **Every triple of block vectors is realised by one parameter.** -/
lemma blk_join (v : Fin 3 → EuclideanSpace ℝ (Fin 4)) :
    ∃ u : EuclideanSpace ℝ (Fin 12), ∀ k : Fin 3, blk k u = v k := by
  refine ⟨(blkSpan 0 (v 0) + blkSpan 1 (v 1) + blkSpan 2 (v 2) :
    EuclideanSpace ℝ (Fin 12)), fun k => ?_⟩
  fin_cases k
  · show (blk 0) (blkSpan 0 (v 0) + blkSpan 1 (v 1) + blkSpan 2 (v 2)) = v 0
    rw [map_add, map_add, blk_blkSpan, blk_blkSpan_of_ne (k := 1) (j := 0) (by decide),
      blk_blkSpan_of_ne (k := 2) (j := 0) (by decide), add_zero, add_zero]
  · show (blk 1) (blkSpan 0 (v 0) + blkSpan 1 (v 1) + blkSpan 2 (v 2)) = v 1
    rw [map_add, map_add, blk_blkSpan_of_ne (k := 0) (j := 1) (by decide), blk_blkSpan,
      blk_blkSpan_of_ne (k := 2) (j := 1) (by decide), zero_add, add_zero]
  · show (blk 2) (blkSpan 0 (v 0) + blkSpan 1 (v 1) + blkSpan 2 (v 2)) = v 2
    rw [map_add, map_add, blk_blkSpan_of_ne (k := 0) (j := 2) (by decide),
      blk_blkSpan_of_ne (k := 1) (j := 2) (by decide), blk_blkSpan, zero_add, zero_add]

/-- **The joint smoothness of a slice of the family**, from the plane data.

This is `Work.Drive.contMDiff_clampedSweep_family` instantiated at the family
`Pp s z = Ξ s (P k z)`, whose joint smoothness is the composition of `ChartPert`'s joint smoothness of
`Ξ` with the smoothness of the plane presentation `P k`. -/
theorem contMDiff_sweepChartSlice_of_family {P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace}
    (hΞ : ChartPert Q 4 Ξ) (hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k))
    (c : Fin 3 → ℝ) (k : Fin 3) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3) =>
        sweepChartSlice P Ξ c k q.1 q.2) := by
  have hPp : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 2) =>
        Ξ q.1 (P k q.2)) := by
    have hfst : ContMDiff
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 2) => q.1) :=
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace ℝ (Fin 2))).contMDiff
    have hsnd : ContMDiff
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 2) => P k q.2) :=
      (hP k).comp
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace ℝ (Fin 2))).contMDiff
    exact hΞ.2.1.comp (hfst.prodMk hsnd)
  have h := contMDiff_clampedSweep_family (c := c k) (ψ := fun r => 1 - r) (by fun_prop)
    (Pp := fun s z => Ξ s (P k z)) hPp
  simpa only [sweepChartSlice] using h

/-- **The joint smoothness of the family from the smoothness of its slices.**  The `k`-th chain of the
family is the slice composed with the block projection, and `blk k` is linear. -/
lemma contMDiff_sweepChartFam (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (c : Fin 3 → ℝ)
    (hslice : ∀ k' : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3) =>
        sweepChartSlice P Ξ c k' q.1 q.2)) (k : Fin 3) :
    ContMDiff (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) =>
        sweepChartFam P Ξ c q.1 k q.2) := by
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) => (blk k q.1, q.2)) :=
    ((blk k).contDiff.comp contDiff_fst).prodMk contDiff_snd
  have h := (hslice k).comp (contMDiff_iff_contDiff.mpr hφ)
  simpa only [Function.comp_def, sweepChartFam_eq_slice] using h

/-- **The smoothness of the slice at a fixed sweep parameter.** -/
lemma contMDiff_sweepChartSlice_point (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (c : Fin 3 → ℝ) (k : Fin 3) (y : EuclideanSpace ℝ (Fin 9))
    (hslice : ∀ k' : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3) =>
        sweepChartSlice P Ξ c k' q.1 q.2)) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : EuclideanSpace ℝ (Fin 4) =>
        sweepChartSlice P Ξ c k s (Work.Drive.TParity.bPartC k y)) := by
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : EuclideanSpace ℝ (Fin 4) => (s, Work.Drive.TParity.bPartC k y)) :=
    contDiff_id.prodMk contDiff_const
  have h := (hslice k).comp (contMDiff_iff_contDiff.mpr hφ)
  simpa only [Function.comp_def] using h

/-- **The charted block derivative** of the `k`-th chain of the design's family at the parameter `t`
and the box point `y`: the change of coordinates of the manifold derivative of the slice. -/
noncomputable def sweepBlockDeriv (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (c : Fin 3 → ℝ)
    (k : Fin 3) (p : CappingSpace) (t : EuclideanSpace ℝ (Fin 12))
    (y : EuclideanSpace ℝ (Fin 9)) : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  (tangentCoordChange (𝓡 4)
      (sweepChartSlice P Ξ c k (blk k t) (Work.Drive.TParity.bPartC k y)) p
      (sweepChartSlice P Ξ c k (blk k t) (Work.Drive.TParity.bPartC k y))) ∘SL
    (mfderiv (𝓡 4) (𝓡 4)
      (fun s : EuclideanSpace ℝ (Fin 4) =>
        sweepChartSlice P Ξ c k s (Work.Drive.TParity.bPartC k y)) (blk k t))

/-- The charted derivative of the `k`-th slice is the block derivative. -/
lemma sweepBlockDeriv_hasFDerivAt (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (c : Fin 3 → ℝ)
    (k : Fin 3) (p : CappingSpace) (t : EuclideanSpace ℝ (Fin 12))
    (y : EuclideanSpace ℝ (Fin 9))
    (hslice : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : EuclideanSpace ℝ (Fin 4) =>
        sweepChartSlice P Ξ c k s (Work.Drive.TParity.bPartC k y)))
    (hsrc : sweepChartSlice P Ξ c k (blk k t) (Work.Drive.TParity.bPartC k y) ∈ (chr p).source) :
    HasFDerivAt (fun s : EuclideanSpace ℝ (Fin 4) =>
      chr p (sweepChartSlice P Ξ c k s (Work.Drive.TParity.bPartC k y)))
      (sweepBlockDeriv P Ξ c k p t y) (blk k t) :=
  fderiv_chart_comp_hasFDerivAt
    (fun s : EuclideanSpace ℝ (Fin 4) =>
      sweepChartSlice P Ξ c k s (Work.Drive.TParity.bPartC k y)) hslice p hsrc

/-- **The explicit charted derivative is onto when the manifold derivative is** (the `∘SL`-form of
`Work.Drive.surjective_fderiv_chart_comp`): the change of coordinates `tangentCoordChange` is injective
between equal-dimensional spaces, hence surjective. -/
theorem surjective_tangentCoordChange_comp_mfderiv {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → CappingSpace}
    {s : EuclideanSpace ℝ (Fin n)} (p : CappingSpace) (hs : f s ∈ (chr p).source)
    (h : Function.Surjective (mfderiv (𝓡 n) (𝓡 4) f s)) :
    Function.Surjective
      (tangentCoordChange (𝓡 4) (f s) p (f s) ∘SL mfderiv (𝓡 n) (𝓡 4) f s) := by
  have hinj : Function.Injective (tangentCoordChange (𝓡 4) (f s) p (f s)) := by
    refine Work.Drive.tangentCoordChange_injective (x := f s) (y := p) (z := f s) ⟨?_, ?_⟩
    · exact mem_extChartAt_source (f s)
    · rw [extChartAt_source]
      exact hs
  have hsurj : Function.Surjective (tangentCoordChange (𝓡 4) (f s) p (f s)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (tangentCoordChange (𝓡 4) (f s) p (f s)).toLinearMap) (by simp)).mp hinj
  exact hsurj.comp h

/-- The block derivative is onto as soon as the manifold derivative of the slice is. -/
lemma surjective_sweepBlockDeriv (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (c : Fin 3 → ℝ)
    (k : Fin 3) (p : CappingSpace) (t : EuclideanSpace ℝ (Fin 12))
    (y : EuclideanSpace ℝ (Fin 9))
    (hsrc : sweepChartSlice P Ξ c k (blk k t) (Work.Drive.TParity.bPartC k y) ∈ (chr p).source)
    (h : Function.Surjective (mfderiv (𝓡 4) (𝓡 4)
      (fun s : EuclideanSpace ℝ (Fin 4) =>
        sweepChartSlice P Ξ c k s (Work.Drive.TParity.bPartC k y)) (blk k t))) :
    Function.Surjective (sweepBlockDeriv P Ξ c k p t y) := by
  exact surjective_tangentCoordChange_comp_mfderiv (n := 4)
    (f := fun s : EuclideanSpace ℝ (Fin 4) =>
      sweepChartSlice P Ξ c k s (Work.Drive.TParity.bPartC k y)) (s := blk k t) p hsrc h

/-- **The `hsurj` hypothesis of the parametric Sard, for the design's family.**

At every zero of the charted difference map the parameter-derivative is onto.  The mechanism: at a
triple meet at most one chain can sit on its *floor* (`y (bIdx k 2) = 0`), because the three truncation
levels `c k` are pairwise distinct and at a floor the chain's value has level exactly `c k` while all
three values at a meet coincide.  The other two chains therefore have nonzero radial parameter, so
their perturbed sweeps supply the surjectivity
(`Work.Drive.surjective_mfderiv_clampedSweep_ne_zero`), through the two relaxed block criteria. -/
theorem hsurj_sweepChartFam (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (c : Fin 3 → ℝ) (hΞ : ChartPert Q 4 Ξ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k')
    (hslice : ∀ k' : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3) =>
        sweepChartSlice P Ξ c k' q.1 q.2))
    (K : Set (EuclideanSpace ℝ (Fin 9))) (p : CappingSpace) {ε : ℝ}
    (hcontain : ∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)),
      ‖t‖ < ε → y ∈ K → ∀ k : Fin 3,
        sweepChartFam P Ξ c t k (Work.Drive.TParity.bPartC k y) ∈ (chr p).source)
    (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9))
    (ht : ‖t‖ < ε) (hy : y ∈ K)
    (hz : Work.Drive.TParity.chartDiff3 p (sweepChartFam P Ξ c t) y = 0) :
    Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin 12) =>
      Work.Drive.TParity.chartDiff3 p (sweepChartFam P Ξ c t') y) t) := by
  classical
  -- ## the meet and the chart containment
  have hsrc : y ∈ Work.Drive.TParity.region3 p (sweepChartFam P Ξ c t) :=
    fun k => hcontain t y ht hy k
  have hmeet : Work.Drive.TParity.meet3 (sweepChartFam P Ξ c t) y :=
    (Work.Drive.TParity.chartDiff3_eq_zero_iff hsrc).mp hz
  have hval : ∀ k : Fin 3, sweepChartFam P Ξ c t k (Work.Drive.TParity.bPartC k y) =
      sweepChartFam P Ξ c t 0 (Work.Drive.TParity.bPartC 0 y) := by
    intro k
    fin_cases k
    · rfl
    · exact hmeet.1.symm
    · exact hmeet.2.symm
  have hlev : ∀ k : Fin 3, levelOf (sweepChartFam P Ξ c t k (Work.Drive.TParity.bPartC k y))
      = levelOf (sweepChartFam P Ξ c t 0 (Work.Drive.TParity.bPartC 0 y)) :=
    fun k => congrArg levelOf (hval k)
  -- ## the block derivatives
  have hsl : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : EuclideanSpace ℝ (Fin 4) =>
        sweepChartSlice P Ξ c k s (Work.Drive.TParity.bPartC k y)) :=
    fun k => contMDiff_sweepChartSlice_point P Ξ c k y hslice
  have hBsrc : ∀ k : Fin 3,
      sweepChartSlice P Ξ c k (blk k t) (Work.Drive.TParity.bPartC k y) ∈ (chr p).source := by
    intro k
    rw [← sweepChartFam_eq_slice]
    exact hcontain t y ht hy k
  have hDf : ∀ k : Fin 3, HasFDerivAt
      (fun t' => chr p (sweepChartFam P Ξ c t' k (Work.Drive.TParity.bPartC k y)))
      ((sweepBlockDeriv P Ξ c k p t y).comp (blk k)) t := by
    intro k
    have hcomp := (sweepBlockDeriv_hasFDerivAt P Ξ c k p t y (hsl k) (hBsrc k)).comp t
      ((blk k).hasFDerivAt)
    simpa only [Function.comp_def, sweepChartFam_eq_slice] using hcomp
  have hBsurj : ∀ k : Fin 3, y (Work.Drive.bIdx k 2) ≠ 0 →
      Function.Surjective (sweepBlockDeriv P Ξ c k p t y) := by
    intro k hk
    refine surjective_sweepBlockDeriv P Ξ c k p t y (hBsrc k) ?_
    have hyne : (Work.Drive.TParity.bPartC k y) 2 ≠ 0 := by
      rw [Work.Drive.TParity.bPartC_apply]
      exact hk
    change Function.Surjective (mfderiv (𝓡 4) (𝓡 4)
      (fun t' => clampedSweep (c k) (fun s => 1 - s) (fun z => Ξ t' (P k z))
        (Work.Drive.TParity.bPartC k y)) (blk k t))
    exact surjective_mfderiv_clampedSweep_ne_zero (P := P k) hΞ (c k) (hc k)
      (Work.Drive.TParity.bPartC k y) hyne (blk k t)
  -- ## at a floor the level is the truncation level
  have hfloor : ∀ k : Fin 3, y (Work.Drive.bIdx k 2) = 0 →
      levelOf (sweepChartFam P Ξ c t k (Work.Drive.TParity.bPartC k y)) = c k := by
    intro k hk
    have h2 : (Work.Drive.TParity.bPartC k y).ofLp 2 = 0 := by
      rw [Work.Drive.TParity.bPartC_apply]
      exact hk
    rw [sweepChartFam_eq_slice, sweepChartSlice,
      clampedSweep_face_zero (c k) (hc k) (fun r => 1 - r)
        (fun z => Ξ (blk k t) (P k z)) (by norm_num)
        (Work.Drive.TParity.bPartC k y) h2]
    exact levelOf_shadow (c k) (hc k) _
  -- ## at most one chain on its floor
  have hAtMost : ∀ k k' : Fin 3, y (Work.Drive.bIdx k 2) = 0 →
      y (Work.Drive.bIdx k' 2) = 0 → k = k' := by
    intro k k' hk hk'
    refine hcdist k k' ?_
    have h1 : c k = levelOf (sweepChartFam P Ξ c t 0 (Work.Drive.TParity.bPartC 0 y)) := by
      rw [← hfloor k hk]; exact hlev k
    have h2 : c k' = levelOf (sweepChartFam P Ξ c t 0 (Work.Drive.TParity.bPartC 0 y)) := by
      rw [← hfloor k' hk']; exact hlev k'
    rw [h1, h2]
  have hfree : ∀ i j l : Fin 3, i ≠ j → i ≠ l →
      Function.Surjective (sweepBlockDeriv P Ξ c i p t y) →
      ∀ z : EuclideanSpace ℝ (Fin 4), ∃ u : EuclideanSpace ℝ (Fin 12),
        ((sweepBlockDeriv P Ξ c i p t y).comp (blk i)) u = z ∧
          ((sweepBlockDeriv P Ξ c j p t y).comp (blk j)) u = 0 ∧
          ((sweepBlockDeriv P Ξ c l p t y).comp (blk l)) u = 0 :=
    fun i j l hij hil hi => pairFree_of_blockSurjective (π := blk)
      (B := fun k => sweepBlockDeriv P Ξ c k p t y)
      (D := fun k => (sweepBlockDeriv P Ξ c k p t y).comp (blk k)) (fun k => rfl) blk_join hij hil hi
  -- ## the case analysis on the (at most one) chain on its floor
  by_cases h0 : y (Work.Drive.bIdx 0 2) = 0
  · have h1ne : y (Work.Drive.bIdx 1 2) ≠ 0 :=
      fun h => absurd (hAtMost 0 1 h0 h) (by decide)
    have h2ne : y (Work.Drive.bIdx 2 2) ≠ 0 :=
      fun h => absurd (hAtMost 0 2 h0 h) (by decide)
    refine Work.Drive.TParity.surjective_fderiv_chartDiff3_of_pair12 12
      (sweepChartFam P Ξ c) p t y (fun k => (sweepBlockDeriv P Ξ c k p t y).comp (blk k)) hDf ?_ ?_
    · exact hfree 1 0 2 (by decide) (by decide) (hBsurj 1 h1ne)
    · exact hfree 2 0 1 (by decide) (by decide) (hBsurj 2 h2ne)
  · by_cases h1 : y (Work.Drive.bIdx 1 2) = 0
    · have h0ne : y (Work.Drive.bIdx 0 2) ≠ 0 := h0
      have h2ne : y (Work.Drive.bIdx 2 2) ≠ 0 :=
        fun h => absurd (hAtMost 1 2 h1 h) (by decide)
      refine Work.Drive.TParity.surjective_fderiv_chartDiff3_of_pair02 12
        (sweepChartFam P Ξ c) p t y (fun k => (sweepBlockDeriv P Ξ c k p t y).comp (blk k)) hDf ?_ ?_
      · exact hfree 0 1 2 (by decide) (by decide) (hBsurj 0 h0ne)
      · exact hfree 2 0 1 (by decide) (by decide) (hBsurj 2 h2ne)
    · have h0ne : y (Work.Drive.bIdx 0 2) ≠ 0 := h0
      have h1ne : y (Work.Drive.bIdx 1 2) ≠ 0 := h1
      refine Work.Drive.TParity.surjective_fderiv_chartDiff3_of_pair01 12
        (sweepChartFam P Ξ c) p t y (fun k => (sweepBlockDeriv P Ξ c k p t y).comp (blk k)) hDf ?_ ?_
      · exact hfree 0 1 2 (by decide) (by decide) (hBsurj 0 h0ne)
      · exact hfree 1 0 2 (by decide) (by decide) (hBsurj 1 h1ne)

/-- **The genericity of the design's triple of chart-perturbed clamped sweeps.**

Given the plane data (`hP`: the three presentations are smooth; `hPseam`: they are seam-invariant), the
`ChartPert` instance, pairwise distinct truncation levels, a compact `K` with the base-locus
containment `hbase` and the chart containment `hcontain` (the two design data), there are arbitrarily
small parameters `t` at which the design's triple satisfies `Work.Drive.Meet3Hyp` — the input of the
triple-counting engines. -/
theorem exists_meet3Hyp_sweepChartFam (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (c : Fin 3 → ℝ) (hΞ : ChartPert Q 4 Ξ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k')
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k))
    (hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → P k y = P k (seamInv2 y))
    (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K) (p : CappingSpace) {ε : ℝ}
    (hε : 0 < ε)
    (hcontain : ∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)),
      ‖t‖ < ε → y ∈ K → ∀ k : Fin 3,
        sweepChartFam P Ξ c t k (Work.Drive.TParity.bPartC k y) ∈ (chr p).source)
    (hbase : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
      Work.Drive.TParity.meet3 (sweepChartFam P Ξ c 0) y → y ∈ interior K) :
    ∀ ε' : ℝ, 0 < ε' →
      ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
        Meet3Hyp CappingSpace (sweepChartFam P Ξ c t) := by
  have hslice : ∀ k' : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3) =>
        sweepChartSlice P Ξ c k' q.1 q.2) :=
    fun k' => contMDiff_sweepChartSlice_of_family hΞ hP c k'
  have hG : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) =>
        sweepChartFam P Ξ c q.1 k q.2) :=
    fun k => contMDiff_sweepChartFam P Ξ c hslice k
  have hsmooth : ∀ (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (sweepChartFam P Ξ c t k) := by
    intro t k
    have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) =>
          ((t, x) : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))) :=
      contDiff_const.prodMk contDiff_id
    have h := (hG k).comp (contMDiff_iff_contDiff.mpr hφ)
    simpa only [Function.comp_def] using h
  have hseam : ∀ (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3)
      (x : EuclideanSpace ℝ (Fin 3)), onSeam x →
      sweepChartFam P Ξ c t k x = sweepChartFam P Ξ c t k (seamInv x) := by
    intro t k x hx
    refine clampedSweep_seamInv (c k) (fun r => 1 - r)
      (fun z => Ξ (blk k t) (P k z)) (fun y hy => ?_) x hx
    rw [hPseam k y hy]
  refine exists_meet3Hyp_of_good_family 12 (sweepChartFam P Ξ c) hG hsmooth hseam K hK hbase
    p hε hcontain ?_
  intro t y ht hy hz
  exact hsurj_sweepChartFam P Ξ c hΞ hc hcdist hslice K p hcontain t y ht hy hz

end

end Work.Drive
