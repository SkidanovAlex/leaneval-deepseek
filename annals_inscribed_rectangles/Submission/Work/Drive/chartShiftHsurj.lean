import Mathlib
import Submission.Work.Drive.projImmersion
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.TParity.ChartDeriv
import Submission.Work.Drive.TParity.LocalGraph
import Submission.Work.Drive.exists_meet3Hyp_of_good_family

/-!
# `hsurj` for the chart-shift family

The parametric-Sard route to the engine's hypotheses (`Work.Drive.exists_meet3Hyp_of_good_family`)
carries a single *design* input besides the containment: the surjectivity of the parameter-derivative
of the charted difference map `Work.Drive.TParity.chartDiff3` at its zeros (`hsurj`).  This file
supplies that input for an explicit family — the **chart-shift** family

`G t k x = (chr p).symm ((chr p) (P k x) + blk k t)`

on the parameter space `ℝ¹² = (ℝ⁴)³` (one `ℝ⁴`-block per chain), where `chr p` is the chart at `p`
and `blk k` is the `k`-th block projection.  Its charted value at any point is the *shift* of the
base charted value by the block `blk k t`, so its parameter-derivative is onto at every point, with
the three blocks independent.

The point of the family is that it needs **no** hypothesis on the base configuration beyond the chart
containment: no immersion of the class map (`hc`), no general position (`hV`), no collision data.  The
three blocks realise the `3` class directions plus the `1` level direction per chain that
`AVOID_LOWDIM_STATUS.md` §10 asks for (see §3bis of the status file for why the level direction is
indispensable, and for the *shape* of a family which cannot have it).

## The exports, in order of use

1. `Work.Drive.TParity.surjective_fderiv_chartDiff3_of_block` — the abstract criterion (charted
   derivatives with the block condition ⟹ `hsurj`), `..._of_directions` (its manifold-level form) and
   `..._of_flow` (its form for a smooth action of `ℝ⁴` in every chain);
2. `Work.Drive.hsurj_chartShiftFamily` and `Work.Drive.hsurj_chartShiftClamped` — the criterion's two
   instances (the clamped one also has *automatic* chart containment);
3. `Work.Drive.clampFun` (+ `exists_clamp`) — the smooth clamp into a ball inside the chart's target;
4. `Work.Drive.exists_meet3Hyp_chartShiftClamped`, `..._of_ball`, `..._of_baseBall` — the lane's
   endpoints: **`∀ ε' > 0, ∃ t, ‖t‖ < ε' ∧ Meet3Hyp M (G t)`**, i.e. the input of the counting engine;
5. `Work.Drive.surjective_projCoordFunDerivE_comp`, `Work.Drive.norm_blk_le` — the two auxiliary
   bricks (the `3` class directions of `End(ℝ⁴)` in the projective chart, and the contraction bound).

Authoritative write-up: `Submission/Work/Drive/CHART_SHIFT_HSURJ_STATUS.md`.
-/

set_option linter.unusedSectionVars false

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-! ## The block machinery on `ℝ¹² = (ℝ⁴)³` -/

/-- The `j`-th coordinate of the `k`-th block of `ℝ¹²` (blocks of four, `k = 0,1,2`). -/
def blkIdx (k : Fin 3) (j : Fin 4) : Fin 12 :=
  ⟨4 * k.val + j.val, by have hk := k.isLt; have hj := j.isLt; omega⟩

/-- **The `k`-th block projection** `ℝ¹² → ℝ⁴`. -/
def blk (k : Fin 3) : EuclideanSpace ℝ (Fin 12) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  ContinuousLinearMap.comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm :
      (Fin 4 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (ContinuousLinearMap.pi (fun j : Fin 4 =>
      PiLp.proj 2 (fun _ : Fin 12 => ℝ) (blkIdx k j)))

lemma blk_apply (k : Fin 3) (t : EuclideanSpace ℝ (Fin 12)) (j : Fin 4) :
    (blk k t).ofLp j = t.ofLp (blkIdx k j) := by
  rw [show (blk k t).ofLp j = ((ContinuousLinearMap.pi (fun j : Fin 4 =>
      PiLp.proj 2 (fun _ : Fin 12 => ℝ) (blkIdx k j))) t) j from rfl]
  rw [ContinuousLinearMap.pi_apply, PiLp.proj_apply]

lemma blkIdx_div (k : Fin 3) (j : Fin 4) : (blkIdx k j).val / 4 = k.val := by
  show (4 * k.val + j.val) / 4 = k.val
  rw [Nat.mul_add_div (by norm_num : 0 < 4), Nat.div_eq_of_lt j.isLt, Nat.add_zero]

lemma blkIdx_mod (k : Fin 3) (j : Fin 4) : (blkIdx k j).val % 4 = j.val := by
  show (4 * k.val + j.val) % 4 = j.val
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]

/-- **The vector concentrated in the `k`-th block.** -/
def blkSpan (k : Fin 3) (z : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 12) :=
  WithLp.toLp 2 (fun i : Fin 12 =>
    if i.val / 4 = k.val then z.ofLp ⟨i.val % 4, Nat.mod_lt _ (by norm_num)⟩ else 0)

lemma blk_blkSpan (k : Fin 3) (z : EuclideanSpace ℝ (Fin 4)) : blk k (blkSpan k z) = z := by
  ext j
  rw [blk_apply, blkSpan, WithLp.ofLp_toLp, blkIdx_div k j, if_pos rfl]
  exact congrArg z.ofLp (Fin.ext (blkIdx_mod k j))

lemma blk_blkSpan_of_ne {k j : Fin 3} (hj : j ≠ k) (z : EuclideanSpace ℝ (Fin 4)) :
    blk j (blkSpan k z) = 0 := by
  ext j'
  rw [blk_apply, blkSpan, WithLp.ofLp_toLp]
  have hne : (blkIdx j j').val / 4 ≠ k.val := by
    rw [blkIdx_div]
    intro h
    exact hj (Fin.ext h)
  rw [if_neg hne]
  rfl

/-! ## The abstract block reduction -/

/-- **The block condition gives `hsurj`.**  Let `G` be a family of triples of `3`-chains in a
`4`-manifold `M`, `p` a point (with chart `chr p`), `t` a parameter and `y` a point of the nine-box.
If the charted derivatives `D k` of the three chains at `(t, y)` admit, in each block `k`, directions
that move the charted value of chain `k` while leaving those of the other two fixed, then the
parameter-derivative of the charted difference map at `(t, y)` is surjective. -/
theorem TParity.surjective_fderiv_chartDiff3_of_block (m : ℕ)
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (p : M) (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9))
    (D : Fin 3 → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (hD : ∀ k : Fin 3, HasFDerivAt
      (fun t' => (Work.Drive.chr p) (G t' k (Work.Drive.TParity.bPartC k y))) (D k) t)
    (hblock : ∀ (k : Fin 3) (z : EuclideanSpace ℝ (Fin 4)),
      ∃ u : EuclideanSpace ℝ (Fin m), D k u = z ∧ ∀ j : Fin 3, j ≠ k → D j u = 0) :
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
    exact (Work.Drive.TParity.pUpCLM_apply ((Work.Drive.chr p) (G t' 0 (Work.Drive.TParity.bPartC 0 y)) -
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
  obtain ⟨u₁, hu₁, hu₁'⟩ := hblock 1 (-w₁)
  obtain ⟨u₂, hu₂, hu₂'⟩ := hblock 2 (-w₂)
  have h1 : D 0 (u₁ + u₂) = 0 := by
    rw [map_add, hu₁' 0 (by decide), hu₂' 0 (by decide), add_zero]
  have h2 : D 1 (u₁ + u₂) = -w₁ := by
    rw [map_add, hu₁, hu₂' 1 (by decide), add_zero]
  have h3 : D 2 (u₁ + u₂) = -w₂ := by
    rw [map_add, hu₁' 2 (by decide), hu₂, zero_add]
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
  refine ⟨u₁ + u₂, ?_⟩
  have hp : ((D 0 - D 1).prod (D 0 - D 2)) (u₁ + u₂) = (w₁, w₂) := by
    rw [ContinuousLinearMap.prod_apply, sub_apply, sub_apply, h1, h2, h3]
    simp
  have hkey : Work.Drive.TParity.pUpCLM
      (((D 0 - D 1).prod (D 0 - D 2)) (u₁ + u₂)) = w := by
    rw [hp, Work.Drive.TParity.pUpCLM_apply w₁ w₂]
    exact hstack
  exact hkey

/-- **`hsurj` from geometric directions** (the form the design uses).

If, at `(t, y)`, the parameter can move the *value* of each chain `k` in **any** tangent direction of
the chart, while freezing the values of the other two chains, then the parameter-derivative of the
charted difference map at `(t, y)` is surjective.  The tangent vector of chain `k` produced by a
parameter `u` is `mfderiv (fun t' => G t' k (bPartC k y)) t u`, transported to the chart by
`tangentCoordChange`; the hypothesis is the geometric statement that these vectors are free per block.
This is the manifold-level form of the block condition of
`Work.Drive.TParity.surjective_fderiv_chartDiff3_of_block`, and it is the precise sense in which a
class perturbation (three directions) *plus* a level perturbation (one direction) per chain gives the
surjectivity of the Sard route. -/
theorem TParity.surjective_fderiv_chartDiff3_of_directions (m : ℕ)
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (p : M) (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9))
    (hsm : ∀ k : Fin 3, ContMDiff (𝓡 m) (𝓡 4) Ctop
      (fun t' => G t' k (Work.Drive.TParity.bPartC k y)))
    (hsrc : ∀ k : Fin 3, G t k (Work.Drive.TParity.bPartC k y) ∈ (Work.Drive.chr p).source)
    (hdir : ∀ (k : Fin 3) (z : EuclideanSpace ℝ (Fin 4)), ∃ u : EuclideanSpace ℝ (Fin m),
      (tangentCoordChange (𝓡 4) (G t k (Work.Drive.TParity.bPartC k y)) p
          (G t k (Work.Drive.TParity.bPartC k y)))
        (mfderiv (𝓡 m) (𝓡 4) (fun t' => G t' k (Work.Drive.TParity.bPartC k y)) t u) = z ∧
      ∀ j : Fin 3, j ≠ k → mfderiv (𝓡 m) (𝓡 4)
          (fun t' => G t' j (Work.Drive.TParity.bPartC j y)) t u = 0) :
    Function.Surjective
      (fderiv ℝ (fun t' => Work.Drive.TParity.chartDiff3 p (G t') y) t) := by
  refine TParity.surjective_fderiv_chartDiff3_of_block (m := m) G p t y
    (fun k => (tangentCoordChange (𝓡 4) (G t k (Work.Drive.TParity.bPartC k y)) p
        (G t k (Work.Drive.TParity.bPartC k y))).comp
      (mfderiv (𝓡 m) (𝓡 4) (fun t' => G t' k (Work.Drive.TParity.bPartC k y)) t)) ?_ ?_
  · intro k
    exact fderiv_chart_comp_hasFDerivAt (fun t' => G t' k (Work.Drive.TParity.bPartC k y))
      (hsm k) p (hsrc k)
  · intro k z
    obtain ⟨u, hu, hu'⟩ := hdir k z
    refine ⟨u, hu, fun j hj => ?_⟩
    change (tangentCoordChange (𝓡 4) (G t j (Work.Drive.TParity.bPartC j y)) p
        (G t j (Work.Drive.TParity.bPartC j y)))
      ((mfderiv (𝓡 m) (𝓡 4) (fun t' => G t' j (Work.Drive.TParity.bPartC j y)) t) u) = 0
    rw [hu' j hj]
    exact map_zero _

/-- **`hsurj` for a family generated by an action of `ℝ⁴` per chain.** -/
theorem TParity.surjective_fderiv_chartDiff3_of_flow
    (Φ : EuclideanSpace ℝ (Fin 4) → M → M)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (p : M) (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9))
    (E : Fin 3 → EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (hΦ : ∀ k : Fin 3, HasFDerivAt (fun s : EuclideanSpace ℝ (Fin 4) =>
        (Work.Drive.chr p) (Φ s (P k (Work.Drive.TParity.bPartC k y)))) (E k) (blk k t))
    (hE : ∀ k : Fin 3, Function.Surjective (E k)) :
    Function.Surjective (fderiv ℝ (fun t' => Work.Drive.TParity.chartDiff3 p
      (fun k x => Φ (blk k t') (P k x)) y) t) := by
  refine TParity.surjective_fderiv_chartDiff3_of_block (m := 12)
    (G := fun t' k x => Φ (blk k t') (P k x)) (p := p) (t := t) (y := y)
    (D := fun k => (E k).comp (blk k)) ?_ ?_
  · intro k
    have hcomp := (hΦ k).comp t ((blk k).hasFDerivAt)
    have hfun : (fun s : EuclideanSpace ℝ (Fin 4) =>
        (Work.Drive.chr p) (Φ s (P k (Work.Drive.TParity.bPartC k y)))) ∘
        (fun t' : EuclideanSpace ℝ (Fin 12) => blk k t')
        = (fun t' : EuclideanSpace ℝ (Fin 12) =>
            (Work.Drive.chr p) (Φ (blk k t') (P k (Work.Drive.TParity.bPartC k y)))) := rfl
    rw [hfun] at hcomp
    exact hcomp
  · intro k z
    obtain ⟨w, hw⟩ := hE k z
    refine ⟨blkSpan k w, ?_, ?_⟩
    · rw [ContinuousLinearMap.comp_apply, blk_blkSpan, hw]
    · intro j hj
      rw [ContinuousLinearMap.comp_apply, blk_blkSpan_of_ne (k := k) hj w, map_zero]

/-! ## The chart-shift family -/

/-- **The chart-shift family.**  `G t k x` is the point of `M` whose chart coordinates are the
chart coordinates of `P k x` shifted by the `k`-th block of `t`. -/
def chartShiftFamily (p : M) (P : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) : M :=
  (chr p).symm ((chr p) (P k x) + blk k t)

/-- The chart-shift family at `t = 0` is the base family (on the chart). -/
lemma chartShiftFamily_zero (p : M) (P : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hP : ∀ k x, P k x ∈ (chr p).source) (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) :
    chartShiftFamily p P 0 k x = P k x := by
  rw [chartShiftFamily, map_zero, add_zero, (chr p).left_inv (hP k x)]

/-- **The chart-shift family satisfies `hsurj`.**  The only hypothesis is the containment of the
shifted charted value in the chart's target. -/
theorem hsurj_chartShiftFamily (p : M) (P : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9))
    (hroom : ∀ k : Fin 3, ((chr p) (P k (TParity.bPartC k y)) + blk k t) ∈ (chr p).target) :
    Function.Surjective
      (fderiv ℝ (fun t' => TParity.chartDiff3 p (chartShiftFamily p P t') y) t) := by
  refine TParity.surjective_fderiv_chartDiff3_of_block (m := 12)
    (G := chartShiftFamily p P) (p := p) (t := t) (y := y) (D := fun k => blk k) ?_ ?_
  · intro k
    refine HasFDerivAt.congr_of_eventuallyEq
      (((blk k).hasFDerivAt).const_add ((chr p) (P k (TParity.bPartC k y)))) ?_
    have hcont : Continuous (fun t' : EuclideanSpace ℝ (Fin 12) =>
        (chr p) (P k (TParity.bPartC k y)) + blk k t') :=
      continuous_const.add (blk k).continuous
    filter_upwards [((chr p).open_target.preimage hcont).mem_nhds (hroom k)] with t' ht'
    show (chr p) (chartShiftFamily p P t' k (TParity.bPartC k y))
      = (chr p) (P k (TParity.bPartC k y)) + blk k t'
    rw [chartShiftFamily]
    exact (chr p).right_inv ht'
  · intro k z
    exact ⟨blkSpan k z, blk_blkSpan k z,
      fun j hj => blk_blkSpan_of_ne (k := k) hj z⟩


/-! ## The clamped chart-shift family: global smoothness

The family `G t k x = (chr p).symm ((chr p) (P k x) + blk k t)` is smooth only as far as the chart
reaches.  Clamping the chart argument into a compact subset of the chart's target (by a smooth
`ψ : ℝ⁴ → ℝ⁴` that is the identity where it matters) makes the family **globally** smooth, keeps the
parameter-derivative equal to `blk k` at the points of interest, and makes the chart containment
**automatic**. -/

/-- **The clamped chart-shift family**: the chart-shift of a chart-resident smooth base `A`, with the
chart argument clamped into the chart's target by `ψ`. -/
def chartShiftClamped (p : M) (ψ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) : M :=
  (chr p).symm (ψ (A k x + blk k t))

/-- The inverse of the chart at `p` is smooth on its target. -/
theorem contMDiffOn_chr_symm (p : M) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) (𝓡 4) Ctop ((chr p).symm) (chr p).target := by
  simpa [Work.Drive.chr] using
    (contMDiffOn_extChartAt_symm (I := 𝓡 4) (x := p) (n := Ctop))

/-- **The clamped chart-shift family is globally smooth** in both the joint sense (the family
smoothness `hG` of the Sard route) and the sliced sense (`hsmooth`). -/
theorem contMDiff_chartShiftClamped (p : M) (ψ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hA : ∀ k, ContDiff ℝ Ctop (A k)) (hψ : ContDiff ℝ Ctop ψ)
    (htarget : ∀ u, ψ u ∈ (chr p).target) :
    (∀ k : Fin 3, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))
        (𝓡 4) Ctop (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) =>
          chartShiftClamped p ψ A q.1 k q.2)) ∧
      (∀ (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3),
        ContMDiff (𝓡 3) (𝓡 4) Ctop (chartShiftClamped p ψ A t k)) := by
  have hsymm := contMDiffOn_chr_symm p
  constructor
  · intro k
    have hinner : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))
        𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) Ctop
        (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) =>
          ψ (A k q.2 + blk k q.1)) := by
      have h1 : ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) =>
          A k q.2 + blk k q.1) := by
        have ha : ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) =>
            A k q.2) := (hA k).comp contDiff_snd
        have hb : ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) =>
            blk k q.1) := (blk k).contDiff.comp contDiff_fst
        exact ha.add hb
      exact (contMDiff_iff_contDiff (𝕜 := ℝ) (n := Ctop)).mpr (hψ.comp h1)
    rw [← contMDiffOn_univ]
    exact hsymm.comp hinner.contMDiffOn (fun q _ => htarget _)
  · intro t k
    have hinner : ContMDiff (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) Ctop
        (fun x : EuclideanSpace ℝ (Fin 3) => ψ (A k x + blk k t)) := by
      have h1 : ContDiff ℝ Ctop (fun x : EuclideanSpace ℝ (Fin 3) => A k x + blk k t) :=
        (hA k).add contDiff_const
      exact (contMDiff_iff_contDiff (𝕜 := ℝ) (n := Ctop)).mpr (hψ.comp h1)
    rw [← contMDiffOn_univ]
    exact hsymm.comp hinner.contMDiffOn (fun x _ => htarget _)

/-- **`hsurj` for the clamped chart-shift family.**  Where the shifted base value stays in the inner
ball `ball c r₁` (on which `ψ` is the identity), the parameter-derivative of the charted difference
map is `blk k` per block, hence onto. -/
theorem hsurj_chartShiftClamped (p : M) (ψ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (htarget : ∀ u, ψ u ∈ (chr p).target)
    (c : EuclideanSpace ℝ (Fin 4)) (r₁ : ℝ)
    (hψid : ∀ u ∈ Metric.ball c r₁, ψ u = u)
    (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9))
    (hroom : ∀ k : Fin 3, A k (TParity.bPartC k y) + blk k t ∈ Metric.ball c r₁) :
    Function.Surjective
      (fderiv ℝ (fun t' => TParity.chartDiff3 p (chartShiftClamped p ψ A t') y) t) := by
  refine TParity.surjective_fderiv_chartDiff3_of_block (m := 12)
    (G := chartShiftClamped p ψ A) (p := p) (t := t) (y := y) (D := fun k => blk k) ?_ ?_
  · intro k
    have hu : A k (TParity.bPartC k y) + blk k t ∈ Metric.ball c r₁ := hroom k
    have hev : (fun u : EuclideanSpace ℝ (Fin 4) => ψ u) =ᶠ[𝓝 (A k (TParity.bPartC k y) + blk k t)]
        id := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hu] with u hu'
      exact hψid u hu'
    have hψ : HasFDerivAt ψ (1 : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
        (A k (TParity.bPartC k y) + blk k t) :=
      (hasFDerivAt_id (A k (TParity.bPartC k y) + blk k t)).congr_of_eventuallyEq hev
    have hcomp : HasFDerivAt
        (fun t' : EuclideanSpace ℝ (Fin 12) =>
          ψ (A k (TParity.bPartC k y) + blk k t'))
        ((1 : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) ∘L blk k) t :=
      hψ.comp t (((blk k).hasFDerivAt).const_add (A k (TParity.bPartC k y)))
    have hder : ((1 : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) ∘L blk k) = blk k := by
      ext v; simp
    rw [hder] at hcomp
    refine hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t' => ?_))
    show (chr p) (chartShiftClamped p ψ A t' k (TParity.bPartC k y))
      = ψ (A k (TParity.bPartC k y) + blk k t')
    rw [chartShiftClamped]
    exact (chr p).right_inv (htarget _)
  · intro k z
    exact ⟨blkSpan k z, blk_blkSpan k z, fun j hj => blk_blkSpan_of_ne (k := k) hj z⟩

/-- **`hsurj` for the chart-shift family with an *arbitrary* clamp `ψ`.**  This is the general form of
`Work.Drive.hsurj_chartShiftClamped`: instead of asking for a ball on which `ψ` is the identity, it asks
only that `ψ` agree with the identity *near each shifted base value*
`A k (bPartC k y) + blk k t` — which is exactly what makes the parameter-derivative `blk k`.  The point
of the generality is that the chart's target is **opaque** (`chartAt` of a charted space built from a
`Homeomorph` is a `Classical.choose`, so no statement about its shape is provable), hence a *ball* inside
it cannot be produced abstractly, while a clamp that is locally the identity on a non-ball region (e.g.
a strip, for a slab-like target) can be supplied by whoever knows the concrete chart. -/
theorem hsurj_chartShift_of_localId (p : M) (ψ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (htarget : ∀ u, ψ u ∈ (chr p).target)
    (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9))
    (hshift : ∀ k : Fin 3, (fun u : EuclideanSpace ℝ (Fin 4) => ψ u) =ᶠ[𝓝 (A k (TParity.bPartC k y) + blk k t)] id) :
    Function.Surjective
      (fderiv ℝ (fun t' => TParity.chartDiff3 p (chartShiftClamped p ψ A t') y) t) := by
  refine TParity.surjective_fderiv_chartDiff3_of_block (m := 12)
    (G := chartShiftClamped p ψ A) (p := p) (t := t) (y := y) (D := fun k => blk k) ?_ ?_
  · intro k
    have hψ : HasFDerivAt ψ (1 : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
        (A k (TParity.bPartC k y) + blk k t) :=
      (hasFDerivAt_id (A k (TParity.bPartC k y) + blk k t)).congr_of_eventuallyEq (hshift k)
    have hcomp : HasFDerivAt
        (fun t' : EuclideanSpace ℝ (Fin 12) =>
          ψ (A k (TParity.bPartC k y) + blk k t'))
        ((1 : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) ∘L blk k) t :=
      hψ.comp t (((blk k).hasFDerivAt).const_add (A k (TParity.bPartC k y)))
    have hder : ((1 : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) ∘L blk k) = blk k := by
      ext v; simp
    rw [hder] at hcomp
    refine hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t' => ?_))
    show (chr p) (chartShiftClamped p ψ A t' k (TParity.bPartC k y))
      = ψ (A k (TParity.bPartC k y) + blk k t')
    rw [chartShiftClamped]
    exact (chr p).right_inv (htarget _)
  · intro k z
    exact ⟨blkSpan k z, blk_blkSpan k z, fun j hj => blk_blkSpan_of_ne (k := k) hj z⟩

/-- **The chart containment of the clamped chart-shift family is automatic.** -/
theorem hcontain_chartShiftClamped (p : M) (ψ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (htarget : ∀ u, ψ u ∈ (chr p).target) (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3)
    (x : EuclideanSpace ℝ (Fin 3)) :
    chartShiftClamped p ψ A t k x ∈ (chr p).source := by
  rw [chartShiftClamped]
  exact (chr p).map_target (htarget _)

/-- **The seam clause of the clamped chart-shift family is inherited from the base `A`.** -/
theorem hseam_chartShiftClamped (p : M) (ψ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hAseam : ∀ k x, Work.Drive.onSeam x → A k (Work.Drive.seamInv x) = A k x)
    (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3))
    (hx : Work.Drive.onSeam x) :
    chartShiftClamped p ψ A t k x = chartShiftClamped p ψ A t k (Work.Drive.seamInv x) := by
  rw [chartShiftClamped, chartShiftClamped, hAseam k x hx]

/-- **The design-facing endpoint of the Sard route with the clamped chart-shift family.**

Everything the parametric-Sard route needs is discharged here, with the *exception* of the three
chart-side/geometry hypotheses that the design controls: the smooth base datum `A` (with its
seam-invariance), the inner-ball containment `hroom` of the shifted base values on `K`, and the
base-triple-locus containment `hbase`.  The output is the engine's input `Meet3Hyp M (G t)` at an
arbitrarily small parameter. -/
theorem exists_meet3Hyp_chartShiftClamped (p : M)
    (ψ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (c : EuclideanSpace ℝ (Fin 4)) (r₁ : ℝ)
    (hA : ∀ k, ContDiff ℝ Ctop (A k)) (hψ : ContDiff ℝ Ctop ψ)
    (htarget : ∀ u, ψ u ∈ (chr p).target)
    (hψid : ∀ u ∈ Metric.ball c r₁, ψ u = u)
    (hAseam : ∀ k x, Work.Drive.onSeam x → A k (Work.Drive.seamInv x) = A k x)
    (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K)
    (hbase : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
      TParity.meet3 (chartShiftClamped p ψ A 0) y → y ∈ interior K)
    {ε : ℝ} (hε : 0 < ε)
    (hroom : ∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)), ‖t‖ < ε →
      y ∈ K → ∀ k : Fin 3, A k (TParity.bPartC k y) + blk k t ∈ Metric.ball c r₁) :
    ∀ ε' : ℝ, 0 < ε' →
      ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
        Meet3Hyp M (chartShiftClamped p ψ A t) := by
  have hsmooth := contMDiff_chartShiftClamped p ψ A hA hψ htarget
  refine exists_meet3Hyp_of_good_family 12 (chartShiftClamped p ψ A) hsmooth.1 hsmooth.2
    (fun t k x hx => hseam_chartShiftClamped p ψ A hAseam t k x hx) K hK hbase p hε ?_ ?_
  · intro t y _ _ k
    exact hcontain_chartShiftClamped p ψ A htarget t k (TParity.bPartC k y)
  · intro t y ht hy _
    exact hsurj_chartShiftClamped p ψ A htarget c r₁ hψid t y (hroom t y ht hy)

/-- **The endpoint for an arbitrary clamp.**  The design supplies a smooth `ψ` valued in the chart's
target (so that the family `G t k x = (chr p).symm (ψ (A k x + blk k t))` is globally smooth and its chart
containment is automatic), a compact `K` containing the base triple locus in its interior, and the
pointwise condition that `ψ` agree with the identity near the shifted base values on `K` — then the Sard
route produces `Meet3Hyp M (G t)` at an arbitrarily small parameter.  All the ball-specific hypotheses of
`Work.Drive.exists_meet3Hyp_chartShiftClamped_of_ball` are gone. -/
theorem exists_meet3Hyp_chartShift_of_localId (p : M)
    (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hA : ∀ k, ContDiff ℝ Ctop (A k))
    (hAseam : ∀ k x, Work.Drive.onSeam x → A k (Work.Drive.seamInv x) = A k x)
    (ψ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (hψ : ContDiff ℝ Ctop ψ) (hψt : ∀ u, ψ u ∈ (chr p).target)
    (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε)
    (hbase : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
      TParity.meet3 (chartShiftClamped p ψ A 0) y → y ∈ interior K)
    (hshift : ∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)), ‖t‖ < ε →
      y ∈ K → ∀ k : Fin 3,
        (fun u : EuclideanSpace ℝ (Fin 4) => ψ u) =ᶠ[𝓝 (A k (TParity.bPartC k y) + blk k t)] id) :
    ∀ ε' : ℝ, 0 < ε' → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
      Meet3Hyp M (chartShiftClamped p ψ A t) := by
  have hsm := contMDiff_chartShiftClamped p ψ A hA hψ hψt
  refine exists_meet3Hyp_of_good_family 12 (chartShiftClamped p ψ A) hsm.1 hsm.2
    (fun t k x hx => hseam_chartShiftClamped p ψ A hAseam t k x hx) K hK hbase p hε ?_ ?_
  · intro t y _ _ k
    exact hcontain_chartShiftClamped p ψ A hψt t k (TParity.bPartC k y)
  · intro t y ht hy _
    exact hsurj_chartShift_of_localId p ψ A hψt t y (hshift t y ht hy)

/-! ## A smooth clamp into a ball -/

/-- **The standard smooth clamp**: identity on `ball c r₁`, valued in `closedBall c r₂`, built from a
`ContDiffBump` at `c`. -/
noncomputable def clampFun (c : EuclideanSpace ℝ (Fin 4)) (r₁ r₂ : ℝ) (h1 : 0 < r₁)
    (h12 : r₁ < r₂) (u : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  c + (⟨r₁, r₂, h1, h12⟩ : ContDiffBump c) u • (u - c)

theorem contDiff_clampFun (c : EuclideanSpace ℝ (Fin 4)) (r₁ r₂ : ℝ) (h1 : 0 < r₁) (h12 : r₁ < r₂) :
    ContDiff ℝ Ctop (clampFun c r₁ r₂ h1 h12) := by
  have hχcont : ContDiff ℝ Ctop
      (fun u : EuclideanSpace ℝ (Fin 4) => (⟨r₁, r₂, h1, h12⟩ : ContDiffBump c) u) :=
    ContDiffBump.contDiff _
  exact contDiff_const.add (hχcont.smul (contDiff_id.sub contDiff_const))

theorem clampFun_eq_self (c : EuclideanSpace ℝ (Fin 4)) (r₁ r₂ : ℝ) (h1 : 0 < r₁) (h12 : r₁ < r₂)
    {u : EuclideanSpace ℝ (Fin 4)} (hu : u ∈ Metric.ball c r₁) :
    clampFun c r₁ r₂ h1 h12 u = u := by
  have hxu : (⟨r₁, r₂, h1, h12⟩ : ContDiffBump c) u = 1 :=
    ContDiffBump.one_of_mem_closedBall _ (Metric.ball_subset_closedBall hu)
  show c + (⟨r₁, r₂, h1, h12⟩ : ContDiffBump c) u • (u - c) = u
  rw [hxu, one_smul, add_sub_cancel]

theorem clampFun_mem_closedBall (c : EuclideanSpace ℝ (Fin 4)) (r₁ r₂ : ℝ) (h1 : 0 < r₁)
    (h12 : r₁ < r₂) (u : EuclideanSpace ℝ (Fin 4)) :
    clampFun c r₁ r₂ h1 h12 u ∈ Metric.closedBall c r₂ := by
  have hle : dist (clampFun c r₁ r₂ h1 h12 u) c ≤ r₂ := by
    have hstep : dist (clampFun c r₁ r₂ h1 h12 u) c
        = (⟨r₁, r₂, h1, h12⟩ : ContDiffBump c) u * dist u c := by
      rw [clampFun, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (ContDiffBump.nonneg _), dist_eq_norm]
    rw [hstep]
    by_cases h : (⟨r₁, r₂, h1, h12⟩ : ContDiffBump c) u = 0
    · rw [h, zero_mul]; linarith
    · have hu : dist u c < r₂ := by
        by_contra hcon
        exact h (ContDiffBump.zero_of_le_dist _ (not_lt.mp hcon))
      have hl1 : (⟨r₁, r₂, h1, h12⟩ : ContDiffBump c) u ≤ 1 := ContDiffBump.le_one _
      have hn0 : 0 ≤ (⟨r₁, r₂, h1, h12⟩ : ContDiffBump c) u := ContDiffBump.nonneg _
      nlinarith [hl1, hn0, (dist_nonneg : (0 : ℝ) ≤ dist u c), hu]
  exact hle

/-- **A smooth clamp** `ψ` that is the identity on `ball c r₁` and maps into `closedBall c r₂`
(`0 < r₁ < r₂`): the existential form of `Work.Drive.clampFun`. -/
theorem exists_clamp (c : EuclideanSpace ℝ (Fin 4)) {r₁ r₂ : ℝ} (h1 : 0 < r₁) (h12 : r₁ < r₂) :
    ∃ ψ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4),
      ContDiff ℝ Ctop ψ ∧ (∀ u ∈ Metric.ball c r₁, ψ u = u) ∧
        (∀ u, ψ u ∈ Metric.closedBall c r₂) :=
  ⟨clampFun c r₁ r₂ h1 h12, contDiff_clampFun c r₁ r₂ h1 h12,
    fun _ hu => clampFun_eq_self c r₁ r₂ h1 h12 hu,
    fun u => clampFun_mem_closedBall c r₁ r₂ h1 h12 u⟩

/-- **The design-facing endpoint of the Sard route, with the clamp constructed.**

From a smooth chart-resident base `A` (seam-invariant), a ball `closedBall c r₂` inside the chart's
target and an inner ball `ball c r₁` containing the shifted base values on the compact `K`, the
clamped chart-shift family of `A` has, **for every `ε' > 0**, a parameter `t` with `‖t‖ < ε'` and the
engine's hypotheses `Meet3Hyp M (chartShiftClamped p (clampFun …) A t)`.

The only geometric inputs are `hbase` (the base triple locus inside `interior K`) and `hroom` (the
inner-ball containment of the shifted base values on `K`); the chart containment `hcontain` and the
surjectivity `hsurj` of the Sard route are *proved* here. -/
theorem exists_meet3Hyp_chartShiftClamped_of_ball (p : M)
    (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hA : ∀ k, ContDiff ℝ Ctop (A k))
    (hAseam : ∀ k x, Work.Drive.onSeam x → A k (Work.Drive.seamInv x) = A k x)
    (c : EuclideanSpace ℝ (Fin 4)) {r₁ r₂ : ℝ} (h1 : 0 < r₁) (h12 : r₁ < r₂)
    (htarget : ∀ u ∈ Metric.closedBall c r₂, u ∈ (chr p).target)
    (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K)
    (hbase : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
      TParity.meet3 (chartShiftClamped p (clampFun c r₁ r₂ h1 h12) A 0) y → y ∈ interior K)
    {ε : ℝ} (hε : 0 < ε)
    (hroom : ∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)), ‖t‖ < ε →
      y ∈ K → ∀ k : Fin 3, A k (TParity.bPartC k y) + blk k t ∈ Metric.ball c r₁) :
    ∀ ε' : ℝ, 0 < ε' → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
      Meet3Hyp M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12) A t) :=
  exists_meet3Hyp_chartShiftClamped p (clampFun c r₁ r₂ h1 h12) A c r₁
    hA (contDiff_clampFun c r₁ r₂ h1 h12)
    (fun u => htarget (clampFun c r₁ r₂ h1 h12 u) (clampFun_mem_closedBall c r₁ r₂ h1 h12 u))
    (fun _ hu => clampFun_eq_self c r₁ r₂ h1 h12 hu) hAseam K hK hbase hε hroom

/-! ## Two reusable bricks of the class-direction mechanism -/

/-- **The class-direction surjectivity in the projective chart.**

For a chart index `i` and a non-zero vector `v` with `v i ≠ 0`, the map
`B ↦ d (projCoordFun i) (v) (B v)` from `End(ℝ⁴)` to the chart space `ℝ³` is **surjective**, i.e. the
projective chart coordinates can be moved in every direction by a linear perturbation of the class.
This is the "`3` class directions per chain" of `AVOID_LOWDIM_STATUS.md` §10, in the chart where they
are visible; it is the concrete ingredient behind `Work.Drive.chartProjMap`-type transports. -/
theorem surjective_projCoordFunDerivE_comp (i : Fin 4) {v : Eucl 3} (hv : v.ofLp i ≠ 0) :
    Function.Surjective
      (fun B : Eucl 3 →L[ℝ] Eucl 3 => projCoordFunDerivE i v (B v)) := by
  have hv0 : v ≠ 0 := fun h => hv (by rw [h]; rfl)
  have htop : LinearMap.range (projCoordFunDerivE i v).toLinearMap = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := LinearMap.finrank_range_add_finrank_ker (projCoordFunDerivE i v).toLinearMap
    have hker : LinearMap.ker (projCoordFunDerivE i v).toLinearMap
        = Submodule.span ℝ ({v} : Set (Eucl 3)) := by
      ext w
      rw [LinearMap.mem_ker]
      exact projCoordFunDerivE_eq_zero_iff hv w
    rw [hker, finrank_span_singleton hv0] at h
    have h4 : Module.finrank ℝ (Eucl 3) = 4 := by simp
    have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    rw [h4] at h
    rw [h3]
    omega
  intro z
  have hz : z ∈ LinearMap.range (projCoordFunDerivE i v).toLinearMap := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨u, hu⟩ := hz
  set φ : Eucl 3 →L[ℝ] ℝ := (v.ofLp i)⁻¹ • PiLp.proj 2 (fun _ : Fin 4 => ℝ) i with hφdef
  refine ⟨φ.smulRight u, ?_⟩
  show (projCoordFunDerivE i v) ((φ.smulRight u) v) = z
  rw [ContinuousLinearMap.smulRight_apply]
  have hφ : φ v = 1 := by
    rw [hφdef, smul_apply, PiLp.proj_apply, smul_eq_mul, inv_mul_cancel₀ hv]
  rw [hφ, one_smul]
  exact hu

/-- **The block projections of `ℝ¹²` are contractions**: `‖blk k t‖ ≤ ‖t‖`.  This is what turns the
inner-ball condition `hroom` of `exists_meet3Hyp_chartShiftClamped_of_ball` into a smallness condition
on `ε`. -/
lemma norm_blk_le (k : Fin 3) (t : EuclideanSpace ℝ (Fin 12)) : ‖blk k t‖ ≤ ‖t‖ := by
  have hinj : Set.InjOn (blkIdx k) (↑(Finset.univ : Finset (Fin 4))) := by
    intro a _ b _ h
    have h' : (blkIdx k a).val = (blkIdx k b).val := congrArg Fin.val h
    have ha := a.isLt; have hb := b.isLt
    simp only [blkIdx] at h'
    exact Fin.ext (by omega)
  have hkey : ‖blk k t‖ ^ 2 ≤ ‖t‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    calc ∑ j : Fin 4, ‖(blk k t).ofLp j‖ ^ 2
        = ∑ j : Fin 4, ‖t.ofLp (blkIdx k j)‖ ^ 2 :=
          Finset.sum_congr rfl (fun j _ => by rw [blk_apply])
      _ = ∑ i ∈ Finset.univ.image (blkIdx k), ‖t.ofLp i‖ ^ 2 :=
          (Finset.sum_image (s := Finset.univ) (g := blkIdx k)
            (f := fun i : Fin 12 => ‖t.ofLp i‖ ^ 2) hinj).symm
      _ ≤ ∑ i ∈ Finset.univ, ‖t.ofLp i‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => by positivity)
  nlinarith [norm_nonneg (blk k t), norm_nonneg t, hkey]

/-- **The inner-ball condition from a base ball.** -/
theorem hroom_of_base_ball
    (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (c : EuclideanSpace ℝ (Fin 4)) {r₁ r' : ℝ}
    (K : Set (EuclideanSpace ℝ (Fin 9)))
    (hbase_ball : ∀ y ∈ K, ∀ k : Fin 3, A k (TParity.bPartC k y) ∈ Metric.closedBall c r')
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ (r₁ - r') / 2) :
    ∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)), ‖t‖ < ε → y ∈ K →
      ∀ k : Fin 3, A k (TParity.bPartC k y) + blk k t ∈ Metric.ball c r₁ := by
  intro t y ht hy k
  rw [Metric.mem_ball]
  have h1 : dist (A k (TParity.bPartC k y)) c ≤ r' :=
    Metric.mem_closedBall.mp (hbase_ball y hy k)
  have h2 : dist (A k (TParity.bPartC k y) + blk k t) c
      ≤ dist (A k (TParity.bPartC k y)) c + ‖blk k t‖ := by
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖A k (TParity.bPartC k y) + blk k t - c‖
        = ‖(A k (TParity.bPartC k y) - c) + blk k t‖ := by
          rw [show A k (TParity.bPartC k y) + blk k t - c
            = (A k (TParity.bPartC k y) - c) + blk k t from by abel]
      _ ≤ ‖A k (TParity.bPartC k y) - c‖ + ‖blk k t‖ := norm_add_le _ _
  have h3 : ‖blk k t‖ ≤ ‖t‖ := norm_blk_le k t
  linarith

/-- **The endpoint with the inner-ball condition reduced to a base ball.** -/
theorem exists_meet3Hyp_chartShiftClamped_of_baseBall (p : M)
    (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hA : ∀ k, ContDiff ℝ Ctop (A k))
    (hAseam : ∀ k x, Work.Drive.onSeam x → A k (Work.Drive.seamInv x) = A k x)
    (c : EuclideanSpace ℝ (Fin 4)) {r₁ r₂ r' : ℝ} (h1 : 0 < r₁) (h12 : r₁ < r₂) (hr' : r' < r₁)
    (htarget : ∀ u ∈ Metric.closedBall c r₂, u ∈ (chr p).target)
    (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K)
    (hbase : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
      TParity.meet3 (chartShiftClamped p (clampFun c r₁ r₂ h1 h12) A 0) y → y ∈ interior K)
    (hbase_ball : ∀ y ∈ K, ∀ k : Fin 3, A k (TParity.bPartC k y) ∈ Metric.closedBall c r') :
    ∀ ε' : ℝ, 0 < ε' → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
      Meet3Hyp M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12) A t) :=
  exists_meet3Hyp_chartShiftClamped_of_ball p A hA hAseam c h1 h12 htarget K hK hbase
    (by linarith : (0 : ℝ) < (r₁ - r') / 2)
    (hroom_of_base_ball A c K hbase_ball (by linarith) le_rfl)

end

end Work.Drive
