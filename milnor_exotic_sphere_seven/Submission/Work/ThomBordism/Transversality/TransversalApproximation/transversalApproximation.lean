import Mathlib
import Submission.Work.ThomBordism.Transversality.Homotopy
import Submission.Work.ThomBordism.Transversality.TransverseSard.LocalRep
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.setup
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.chi
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.chiTilde
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.chartBridge
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.perturbation
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.volume_badSet_eq_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000



/-!
# The transversality homotopy theorem (item 2a of the Transversality chapter)

This file proves `Work.ThomBordism.Transversality.TransversalApproximation`: for a compact `T2`
smooth manifold `M` with boundary, a `CoreTarget` `X` and a `C^∞` map `F : M → X.E` which is
transverse to the core on a neighbourhood of `∂M`, there are `F' : M → X.E`, `C^∞` and transverse to
the core everywhere, and a `C^∞` homotopy `H : M × ℝ → X.E` from `F` to `F'` which is constant on
`∂M`.

## The proof, in five steps

All the *mathematics* of the proof is standard (the "transversality homotopy theorem", see e.g.
Hirsch, *Differential Topology*, Theorem 2.2.4, or Bredon, Theorem VI.2.6); the work is to build the
manifold-level bookkeeping that Mathlib does not have.

Throughout, write `G := Φ ∘ F : M → ℝ^k` and `T := {x : M | IsTransverseAt X I F x}` (open, by
`isOpen_setOf_isTransverseAt`), so that `∂M ⊆ T` by hypothesis and `Tᶜ ⊆ F ⁻¹' (X.core)`.

**Step 1 (done, `TransversalApproximation.chi`).**  A smooth `χ : M → [0,1]`, vanishing on a
neighbourhood `V` of `∂M`, positive off `T`
(`exists_contMDiff_vanishingNearBoundary_pos_off`, proved there).  Consequently, for the smooth
nonnegative function

`χ̃ := χ * (β ∘ F)`,  `β := β̂ ∘ Φ : E → [0,1]`,  `β̂ = 1` near `0`, `supp β̂` a small ball,

we have `χ̃ x = 0` for `x ∈ V` (so the homotopy is constant near `∂M`), and `χ̃ x > 0` at every
interior point with `G x = 0`: if `G x = 0` then `F x ∈ core`, hence `β (F x) = 1` and `x ∉ T`, so
`χ x > 0`.  (The `β`-factor also guarantees that the perturbation is supported near the core, over a
compact set `K := F (supp χ) ∩ supp β ⊆ V₀ := {y : IsSubmersionAt Φ y}`, whose existence is a
*compactness* argument: `F (supp χ) ∩ (E ∖ V₀)` is compact and disjoint from `core = Φ ⁻¹' {0}`, so
`‖Φ‖` is bounded below by `δ > 0` there.)

**Step 2 (the box families).**  For every point `y₀ ∈ V₀` there is a smooth
`Ψ : E → ℝ^k → E` and an open `U ∋ y₀`, `ε > 0`, with `Ψ y 0 = y`,
`Φ (Ψ y t) = Φ y + t` and `Ψ y t ∈ U` for `y ∈ U`, `‖t‖ ≤ ε`
(the *closed form* `y ↦ (domChart)⁻¹ (equiv⁻¹ (codChart (Φ y + t), (equiv (domChart y))₂))`
from the submersion normal form `IsSubmersionAtOfComplement.writtenInCharts`, glued with the identity
by a bump in the chart coordinates so that it is globally smooth).

**Step 3 (the perturbation).**  Cover the compact set `K` by finitely many boxes `U_1, …, U_N` with
families `Ψ^1, …, Ψ^N`.  Choose a *finite* smooth partition of unity `ρ_1, …, ρ_N` of `M` subordinate
to `x ↦ F x ∈ U_i` (Mathlib: `SmoothPartitionOfUnity.exists_isSubordinate`), and define

`F' t x := Ψ^N (ρ_N x • χ̃ x • t) (… (Ψ^1 (ρ_1 x • χ̃ x • t) (F x)) …)`.

Every factor is globally smooth, and by the *exact additivity* of step 2 applied inductively we get,
for `‖t‖` small enough,

`Φ (F' t x) = G x + χ̃ x • t`   for **all** `x : M`.

The induction needs the intermediate points to lie in the boxes; this is
`exists_uniform_ball_of_isCompact` (`TransversalApproximation.setup`, proved), applied to the
(finitely many, smooth) intermediate maps `x ↦ (the point after j steps)`, whose value at `t = 0` is
`F x ∈ U_{j+1}` whenever `ρ_{j+1} x ≠ 0`.

**Step 4 (Sard / choice of the parameter).**  By Sard's theorem the set

`B := {t : ∃ x, x is an interior point ∧ χ̃ x ≠ 0 ∧ G x = χ̃ x • t ∧ x is not a regular point of x ↦ G x - χ̃ x • t}`

is null.  This is `Sard.sardParametric` (`Sard/sardParametric.lean`, proved) applied *in charts of
`M`*: `M` is compact, so finitely many charts cover it, and `FiniteDimensional ℝ E'` follows from
compactness + `T2Space` (`FiniteDimensional.of_locallyCompact_manifold`), so each chart expression is
a map on an open subset of a Euclidean space.  Choose `t` with `‖t‖` small and `t ∉ B`, using that a
null set has dense complement.

**Step 5 (transversality of `F' := F' t` and the homotopy).**  Let `x : M` with `Φ (F' x) = 0`, i.e.
`G x + χ̃ x • t = 0`.

* If `χ̃ x ≠ 0` (in particular `x` is an interior point, since `χ̃ = 0` near `∂M`): then `x` is a
  witness for `t ∈ B` with the sign of `t` reversed, and `t ∉ B` says that the derivative of
  `x ↦ G x - χ̃ x • (−t) = Φ ∘ F'` at `x` is *surjective*; since `x` is an interior point,
  surjectivity of `mfderiv` implies `IsSubmersionAt`
  (`submersionAt_of_mfderiv_surjective`, delegated).
* If `χ̃ x = 0`: then `F' x = F x ∈ core`, hence `χ x = 0`, i.e. `x ∈ T`, so `Φ ∘ F` is a
  submersion at `x`; by `mfderiv_surjective_of_submersionAt` (delegated) the derivative of `G` at `x`
  is surjective, and since `mfderiv χ̃ x = 0` (the cut-off is nonnegative and vanishes at `x`) the
  derivative of `Φ ∘ F'` at `x` is the same, hence surjective; again `IsSubmersionAt` follows from
  `submersionAt_of_mfderiv_surjective`.
* If `x ∈ ∂M`: then `x ∈ V`, so `χ̃` vanishes on a whole neighbourhood of `x` and `F' = F` there;
  `IsTransverseAt X I F' x` follows from `IsTransverseAt X I F x` by
  `isTransverseAt_of_eventuallyEq`, and the latter is the hypothesis.

Finally `H (x, s) := F' (s • t) x` is a smooth homotopy from `F` to `F'`, constant on `∂M` (where
`χ̃ = 0`), giving `HomotopicRelBoundary I X F F'`.

## STATUS (important finding): the target `X.E` need not be Hausdorff

The scheme above glues *local* vertical-translation families into *globally defined* smooth maps
`Ψ : E → ℝ^k → E` (using a smooth bump on `E`), because the composition of the finitely many steps
must be a map defined on all of `E`.  This is **impossible in general**: `CoreTarget` imposes no
separation axiom on `E`, and the delegated lemma `exists_boxFamily` was machine-refuted
(`Submission/Work/ThomBordism/Transversality/BoxFamily/Counterexample.lean`,
`BoxFamily.not_exists_boxFamily_universal`) using the "line with two origins"
`E = (ℝ∖{0}) ∪ {o₀, o₁}` with `Φ` the coordinate: there, *no* smooth `Ψ` with `Ψ y 0 = y` and
`Φ (Ψ y t) = Φ y + t` near `o₀` exists, because continuity of `Ψ` at `(o₀, 0)` and at `(o₁, 0)`
would force a sequence with values in `{o₀, o₁}` to converge to both origins at once.

The corrected statement, with the hypothesis `[T2Space E]` (which supplies the smooth bumps), is
proved in `Submission/Work/ThomBordism/Transversality/BoxFamily/Fix.lean`
(`BoxFamily.exists_boxFamily_of_t2`).  So the construction of steps 2–3 above goes through verbatim
for Hausdorff targets.

**Consequence for this file.**  Since `TransversalApproximation` quantifies over *arbitrary*
`CoreTarget`s (no `T2Space X.E`), the five-step proof above must be replaced by an argument which
does not move points of `E`.  My own attempts at a counterexample to the *theorem* on the line with
two origins all failed (in the simplest cases the perturbation can avoid the core altogether, and the
"coordinate" homotopy near a bad interior zero is continuous because a sequence with coordinate
tending to `0` converges to both origins), so the theorem is plausibly true and a *construction*
(rather than a disproof) is what is missing.  Two candidate routes:

1. do everything on the source: for each point `x : M` a chart of `E` around `F x` and a chart of
   `M`, glue the *perturbations* along a partition of unity of `M` subordinate to the (finite) cover
   by sets on which `F` lands in one box — the difficulty is that the glued *values* must lie in a
   common chart of `E`;
2. replace the vertical translations by a perturbation of the *source* maps
   `F ↦ (a smooth family of local diffeomorphisms of M) ∘ F` — this cannot change the intersection
   pattern of `F` with the core, so it is not enough by itself.

## What is proved here, and what is delegated

* `TransversalApproximation.setup` — `exists_uniform_ball_of_isCompact` (step 3, proved).
* `TransversalApproximation.chi` — the cut-off `χ` (step 1, proved).
* `.../submersionAt_of_mfderiv_surjective`, `.../mfderiv_surjective_of_submersionAt` — the two
  directions of "at an interior point, `IsSubmersionAt` ⟺ `mfderiv` is surjective" (steps 5,
  5bis); these are open TODOs of Mathlib's `Geometry/Manifold/Submersion.lean`.
* `.../exists_boxFamily` — step 2.
* `.../volume_badSet_eq_zero` — step 4 (the manifold-level Sard statement).
* The assembly (steps 3, 5) is below.
-/


open scoped Manifold ContDiff
open Function Set Topology Manifold Filter MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace Work.ThomBordism.Transversality.TransversalApproximation

noncomputable section

open Work.ThomBordism.Transversality (CoreTarget)

variable {n k : ℕ}

/-- **The local representation of a global `C^∞` map in a chart of the maximal atlas is `C^∞` on
the interior of the chart target.** -/
theorem contDiffOn_localRep_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {G : M → F'} (hG : ContMDiff I (modelWithCornersSelf ℝ F') ((⊤ : ℕ∞) : WithTop ℕ∞) G)
    {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ((⊤ : ℕ∞) : WithTop ℕ∞) M) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : E => G ((e.extend I).symm v))
      (interior ((e.extend I).target)) := by
  have h1 : ContMDiffOn 𝓘(ℝ, E) I ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : E => (e.extend I).symm v)
      (I '' e.target) := contMDiffOn_extend_symm he
  have h2 : ContMDiffOn I (modelWithCornersSelf ℝ F') ((⊤ : ℕ∞) : WithTop ℕ∞) G univ :=
    fun x _ => hG x
  have h3 : ContMDiffOn 𝓘(ℝ, E) (modelWithCornersSelf ℝ F') ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : E => G ((e.extend I).symm v)) (I '' e.target) := h2.comp h1 (fun v _ => trivial)
  rw [contMDiffOn_iff_contDiffOn] at h3
  rw [OpenPartialHomeomorph.extend_target']
  exact h3.mono interior_subset

set_option backward.isDefEq.respectTransparency false

/-- **At an interior point, a surjective `mfderiv` makes a `C^∞` map a submersion.** -/
theorem isSubmersionAt_of_surjective_mfderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] {k : ℕ}
    {G : M → EuclideanSpace ℝ (Fin k)} (hG : ContMDiff I (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) G)
    {x : M} (hx : I.IsInteriorPoint x) (hGx : G x = 0)
    (hsurj : Function.Surjective (mfderiv I (𝓡 k) G x)) :
    Manifold.IsSubmersionAt I (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) G x := by
  have he : chartAt H x ∈ IsManifold.maximalAtlas I ((⊤ : ℕ∞) : WithTop ℕ∞) M :=
    IsManifold.chart_mem_maximalAtlas x
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxi : x ∉ I.boundary M := fun h => (I.isInteriorPoint_iff_not_isBoundaryPoint x).mp hx h
  have hVx : ((chartAt H x).extend I) x ∈ interior (((chartAt H x).extend I).target) :=
    (ModelWithCorners.isInteriorPoint_iff (I := I) (x := x)).mp hx
  have hrep := contDiffOn_localRep_interior I hG he
  have hsurj' : Function.Surjective
      (fderiv ℝ (fun v : E => G (((chartAt H x).extend I).symm v)) (((chartAt H x).extend I) x)) :=
    (surjective_mfderiv_iff_surjective_fderiv_extChartAt I hx
      ((hG x).mdifferentiableAt (by simp))).mp hsurj
  exact TransverseSard.isSubmersionAt_of_surjective_fderiv_localRep I he hxsrc hxi hGx
    isOpen_interior hVx interior_subset hrep hsurj'


/-- **The derivative of `y ↦ χ y • t` at a local minimum of `χ` vanishes.** -/
theorem mfderiv_smul_const_eq_zero_of_isLocalMin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] {k : ℕ} {χ : M → ℝ}
    (hχ : ContMDiff I (𝓘(ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) χ) {x : M} (hmin : IsLocalMin χ x)
    (hx : I.IsInteriorPoint x) (t : EuclideanSpace ℝ (Fin k)) :
    mfderiv I (𝓡 k) (fun y => χ y • t) x = 0 := by
  set z0 : E := (extChartAt I x) x with hz0
  set ψ : E → ℝ := fun v => χ ((extChartAt I x).symm v) with hψ
  have hcoe : (extChartAt I x).symm z0 = x := by
    rw [hz0]; exact (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
  have hcoe' : (extChartAt I x).symm ((extChartAt I x) x) = x := by
    rw [← hz0]; exact hcoe
  have hmem : z0 ∈ interior (Set.range I) := by
    rw [ModelWithCorners.isInteriorPoint_iff] at hx
    exact interior_mono (extChartAt_target_subset_range (I := I) x) hx
  have hnhds : Set.range I ∈ 𝓝 z0 :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hmem) interior_subset
  have hwritten : writtenInExtChartAt I (𝓡 k) x (χ • (fun _ : M => t)) =
      fun v : E => χ ((extChartAt I x).symm v) • t := by
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply]
    rw [extChartAt_self_eq]
    rfl
  have hχχ : HasFDerivWithinAt ψ (mfderiv I (𝓘(ℝ)) χ x) (Set.range I) z0 := by
    have h := ((hχ x).mdifferentiableAt (by simp)).hasMFDerivAt
    unfold HasMFDerivAt at h
    exact h.2
  have hψmin : IsLocalMin ψ z0 := by
    have htend : Tendsto (fun z => (extChartAt I x).symm z) (𝓝 z0) (𝓝 x) := by
      simpa only [hcoe'] using (continuousAt_extChartAt_symm (I := I) x).tendsto
    filter_upwards [htend.eventually hmin] with z hz
    simpa only [hψ, hcoe] using hz
  have h1 : HasFDerivWithinAt (fun v : E => χ ((extChartAt I x).symm v) • t)
      (mfderiv I (𝓡 k) (fun y => χ y • t) x) (Set.range I) z0 := by
    have hconst : ContMDiffAt I (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : M => t) x :=
      contMDiffAt_const
    have h := (((hχ x).smul hconst).mdifferentiableAt (by simp)).hasMFDerivAt
    unfold HasMFDerivAt at h
    rw [hwritten] at h
    exact h.2
  have h2 : fderiv ℝ (fun v : E => χ ((extChartAt I x).symm v) • t) z0 =
      mfderiv I (𝓡 k) (fun y => χ y • t) x :=
    (h1.hasFDerivAt hnhds).fderiv
  have hψdiff : DifferentiableAt ℝ ψ z0 := (hχχ.hasFDerivAt hnhds).differentiableAt
  have hzero : fderiv ℝ (fun v : E => χ ((extChartAt I x).symm v) • t) z0 = 0 := by
    rw [(hψdiff.hasFDerivAt.smul_const t).fderiv, hψmin.fderiv_eq_zero]
    ext v
    simp
  rw [← h2, hzero]

/-- **The transversality homotopy theorem** (see `Homotopy.lean`). -/
theorem transversalApproximation : Work.ThomBordism.Transversality.TransversalApproximation := by
  intro n k E' H _ _ _ I X M _ _ _ _ _ F hF htr
  classical
  by_cases hM : Nonempty M
  · haveI : Nonempty M := hM
    haveI : FiniteDimensional ℝ E' := finiteDimensional_model (M := M) I
    obtain ⟨U, hUbd, hUopen, hUtr⟩ := htr
    obtain ⟨χ, hχ, hχ0, hχ1, hχV, hχpos⟩ :=
      exists_contMDiff_vanishingNearBoundary_pos_off I hUopen hUbd
    obtain ⟨V, hVopen, hVbd, hV0⟩ := hχV
    obtain ⟨χt, hχt, hχt0, hχt1, hχtV, hχtcore, hχtsupp⟩ :=
      exists_chiTilde I X F hF χ hχ hχ0 hχ1 ⟨V, hVopen, hVbd, hV0⟩
    obtain ⟨Vt, hVtopen, hVtbd, hVt0⟩ := hχtV
    obtain ⟨ε₁, hε₁, 𝒢, h𝒢sm, h𝒢0, h𝒢add, h𝒢van⟩ :=
      exists_perturbation I X F hF χt hχt hχt0 hχt1 hχtsupp
    -- the bad set of parameters
    have hG0sm : ContMDiff I (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => X.Φ (F y)) :=
      X.contMDiff_Φ.comp hF
    set Bad : Set (EuclideanSpace ℝ (Fin k)) := {t |
        ∃ x, I.IsInteriorPoint x ∧ 0 < χt x ∧ (fun y => X.Φ (F y)) x = χt x • t ∧
          ¬ Function.Surjective
            (mfderiv I (𝓡 k) (fun y => X.Φ (F y) - χt y • t) x)} with hBad
    have hB : volume Bad = 0 := by
      rw [hBad]
      exact volume_badSet_eq_zero I (fun y => X.Φ (F y)) hG0sm χt hχt hχt0
    have hε3 : 0 < ε₁ / 3 := by linarith
    obtain ⟨t, htBad, htball⟩ : ∃ t ∉ Bad, t ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (ε₁ / 3) := by
      by_contra h
      push_neg at h
      have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (ε₁ / 3) ⊆ Bad := by
        intro u hu
        by_contra hc
        exact h u hc hu
      have hle : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (ε₁ / 3)) ≤ volume Bad :=
        measure_mono hsub
      rw [hB, le_zero_iff] at hle
      exact absurd hle (ne_of_gt (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin k)) hε3))
    have htε : ‖t‖ < ε₁ := by
      have h := Metric.mem_ball.mp htball
      rw [dist_eq_norm, sub_zero] at h
      linarith
    have ht3 : 3 * ‖t‖ < ε₁ := by
      have h := Metric.mem_ball.mp htball
      rw [dist_eq_norm, sub_zero] at h
      linarith
    -- the perturbed map and the composite
    have hmaps : ∀ x : M,
        (x, -t) ∈ Set.univ ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ε₁ :=
      fun x => ⟨trivial, by
        simpa [Metric.mem_ball, dist_eq_norm, sub_zero, norm_neg] using htε⟩
    have hF'sm : ContMDiff I (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => 𝒢 x (-t)) := by
      intro x
      have hpair : ContMDiffAt I (I.prod (𝓡 k)) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : M => (y, -t)) x := contMDiffAt_id.prodMk contMDiffAt_const
      exact (h𝒢sm.contMDiffAt ((isOpen_univ.prod Metric.isOpen_ball).mem_nhds (hmaps x))).comp x hpair
    have hcompsm : ContMDiff I (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => X.Φ (𝒢 y (-t))) := X.contMDiff_Φ.comp hF'sm
    have hsub_eq : ∀ y : M, X.Φ (𝒢 y (-t)) = X.Φ (F y) - χt y • t := by
      intro y
      rw [h𝒢add y (-t) (by simpa [norm_neg] using htε), smul_neg, sub_eq_add_neg]
    refine ⟨fun x => 𝒢 x (-t), hF'sm, ?_, ?_⟩
    · -- transversality
      rw [isTransverse_def]
      intro x
      rw [isTransverseAt_def]
      intro hcore
      change Manifold.IsSubmersionAt I (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => X.Φ (𝒢 y (-t))) x
      have hG0eq : X.Φ (F x) = χt x • t := by
        have h := h𝒢add x (-t) (by simpa [norm_neg] using htε)
        rw [h, smul_neg, ← sub_eq_add_neg, sub_eq_zero] at hcore
        exact hcore
      by_cases hxV : x ∈ Vt
      · -- `F' = F` near `x`
        have hχtx : χt x = 0 := hVt0 x hxV
        have hG0x : X.Φ (F x) = 0 := by rw [hG0eq, hχtx, zero_smul]
        have hev : (fun y => X.Φ (𝒢 y (-t))) =ᶠ[𝓝 x] (fun y => X.Φ (F y)) := by
          filter_upwards [hVtopen.mem_nhds hxV] with y hy
          exact congrArg X.Φ
            (h𝒢van y (by filter_upwards [hVtopen.mem_nhds hy] with z hz; exact hVt0 z hz) (-t))
        have hxU : x ∈ U := by
          by_contra hxU
          have h1 : 0 < χ x := hχpos x hxU
          have h2 : χt x = χ x := hχtcore x hG0x
          linarith [hχtx]
        have hsub : Manifold.IsSubmersionAt I (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun y => X.Φ (F y)) x :=
          (isTransverseAt_iff_of_mem_core I hG0x).mp (hUtr x hxU)
        exact (Manifold.IsSubmersionAt.congr_iff hev).mpr hsub
      · have hint : I.IsInteriorPoint x :=
          (I.isInteriorPoint_iff_not_isBoundaryPoint x).mpr fun hb => hxV (hVtbd hb)
        by_cases hχtx : χt x = 0
        · -- the derivative of `χt · t` vanishes at the minimum `x`
          have hG0x : X.Φ (F x) = 0 := by rw [hG0eq, hχtx, zero_smul]
          have hmin : IsLocalMin χt x :=
            Filter.Eventually.of_forall fun y => by rw [hχtx]; exact hχt0 y
          have hxU : x ∈ U := by
            by_contra hxU
            have h1 : 0 < χ x := hχpos x hxU
            have h2 : χt x = χ x := hχtcore x hG0x
            linarith [hχtx]
          have hsub : Manifold.IsSubmersionAt I (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞)
              (fun y => X.Φ (F y)) x :=
            (isTransverseAt_iff_of_mem_core I hG0x).mp (hUtr x hxU)
          have hsurjF : Function.Surjective (mfderiv I (𝓡 k) (fun y => X.Φ (F y)) x) :=
            mfderiv_surjective_of_submersionAt I hint hsub
          have hmd1 : MDifferentiableAt I (𝓡 k) (fun y => X.Φ (F y)) x :=
            (hG0sm x).mdifferentiableAt (by simp)
          have hmd2 : MDifferentiableAt I (𝓡 k) (fun y => χt y • t) x :=
            ((hχt x).smul (contMDiffAt_const (c := t))).mdifferentiableAt (by simp)
          have hsmul : mfderiv I (𝓡 k) (fun y => χt y • t) x = 0 :=
            mfderiv_smul_const_eq_zero_of_isLocalMin I hχt hmin hint t
          have hderiv : mfderiv I (𝓡 k) (fun y => X.Φ (F y) - χt y • t) x =
              mfderiv I (𝓡 k) (fun y => X.Φ (F y)) x := by
            rw [show (fun y => X.Φ (F y) - χt y • t) =
                (fun y => X.Φ (F y)) + -(fun y => χt y • t) from by
              funext y; simp [sub_eq_add_neg]]
            rw [mfderiv_add hmd1 hmd2.neg]
            rw [show mfderiv I (𝓡 k) (-(fun y => χt y • t)) x = 0 from by
              rw [mfderiv_neg, hsmul, neg_zero]]
            rw [add_zero]
          have hsurj : Function.Surjective (mfderiv I (𝓡 k) (fun y => X.Φ (𝒢 y (-t))) x) := by
            rw [show (fun y => X.Φ (𝒢 y (-t))) = fun y => X.Φ (F y) - χt y • t from
              funext hsub_eq]
            rw [hderiv]
            exact hsurjF
          exact isSubmersionAt_of_surjective_mfderiv I hcompsm hint hcore hsurj
        · -- the Sard condition gives surjectivity
          have hpos : 0 < χt x := lt_of_le_of_ne (hχt0 x) (Ne.symm hχtx)
          have hs : Function.Surjective
              (mfderiv I (𝓡 k) (fun y => X.Φ (F y) - χt y • t) x) := by
            by_contra hcon
            exact htBad (by rw [hBad]; exact ⟨x, hint, hpos, hG0eq, hcon⟩)
          have hsurj : Function.Surjective (mfderiv I (𝓡 k) (fun y => X.Φ (𝒢 y (-t))) x) := by
            rw [show (fun y => X.Φ (𝒢 y (-t))) = fun y => X.Φ (F y) - χt y • t from
              funext hsub_eq]
            exact hs
          exact isSubmersionAt_of_surjective_mfderiv I hcompsm hint hcore hsurj
    · -- the homotopy
      obtain ⟨sg, hsg_sm, hsg0, hsg1, hsg_le⟩ : ∃ sg : ℝ → ℝ,
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sg ∧ sg 0 = 0 ∧ sg 1 = 1 ∧ ∀ s, |sg s| ≤ 3 := by
        let bb : ContDiffBump (0 : ℝ) := ⟨2, 3, by norm_num, by norm_num⟩
        refine ⟨fun s => s * bb s, ?_, ?_, ?_, ?_⟩
        · exact contDiff_id.mul (bb.contDiff (n := (⊤ : ℕ∞)))
        · simp
        · have h1 : bb (1 : ℝ) = 1 := bb.one_of_mem_closedBall (by
            rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_one]
            norm_num)
          simp [h1]
        · intro s
          by_cases hs : dist s (0 : ℝ) ≤ 3
          · have hbb : |bb s| ≤ 1 := by
              rw [abs_of_nonneg bb.nonneg]; exact bb.le_one
            calc |s * bb s| = |s| * |bb s| := abs_mul s _
              _ ≤ 3 * 1 := mul_le_mul (by rwa [Real.dist_eq, sub_zero] at hs) hbb (abs_nonneg _)
                  (by norm_num)
              _ = 3 := by norm_num
          · have hbb : bb s = 0 := bb.zero_of_le_dist (le_of_lt (not_le.mp hs))
            simp [hbb]
      refine ⟨fun p : M × ℝ => 𝒢 p.1 (sg p.2 • (-t)), ?_, ?_, ?_, ?_⟩
      · have hpair : ContMDiff (I.prod (𝓘(ℝ))) (I.prod (𝓡 k)) ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun p : M × ℝ => (p.1, sg p.2 • (-t))) :=
          contMDiff_fst.prodMk ((hsg_sm.comp_contMDiff contMDiff_snd).smul contMDiff_const)
        have hmaps' : ∀ p : M × ℝ,
            (p.1, sg p.2 • (-t)) ∈ Set.univ ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ε₁ := by
          intro p
          refine ⟨trivial, ?_⟩
          rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs]
          calc |sg p.2| * ‖-t‖ ≤ 3 * ‖t‖ := by
                rw [norm_neg]
                exact mul_le_mul_of_nonneg_right (hsg_le p.2) (norm_nonneg _)
            _ < ε₁ := ht3
        intro p
        exact (h𝒢sm.contMDiffAt
          ((isOpen_univ.prod Metric.isOpen_ball).mem_nhds (hmaps' p))).comp p (hpair p)
      · intro x
        change 𝒢 x (sg 0 • (-t)) = F x
        rw [hsg0, zero_smul, h𝒢0]
      · intro x
        change 𝒢 x (sg 1 • (-t)) = 𝒢 x (-t)
        rw [hsg1, one_smul]
      · intro x hxbd s
        have hxV : x ∈ Vt := hVtbd hxbd
        exact h𝒢van x (by
          filter_upwards [hVtopen.mem_nhds hxV] with z hz
          exact hVt0 z hz) (sg s • (-t))
  · haveI : IsEmpty M := not_nonempty_iff.mp hM
    exact ⟨F, hF, fun x => isEmptyElim x, homotopicRelBoundary_refl I X hF⟩

end

end Work.ThomBordism.Transversality.TransversalApproximation
